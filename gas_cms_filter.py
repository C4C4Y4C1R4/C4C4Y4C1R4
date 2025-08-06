#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# Ultra-Optimized Keyword Extractor v3.1.10
# Extracts lines containing keywords with superior performance, auto-deduplication,
# robust resume capability, and parallel execution support, outputting corrected JSONL.
# v3.1.5: Reverted parsing to original pre-v3.1.3 behavior (no http/s removal, 1 separator = user:pass).
# v3.1.6: Code finalization and minor bug fixes.
# v3.1.7: Fixed reported IndentationError, SyntaxError, AttributeError related to KB input check and file locking.
# v3.1.8: Fixed indentation error in FileLock.release causing NameError, reviewed code structure.
# v3.1.9: Added validation logic for URL, Username, and Password fields.
# v3.1.10: Fixed NameError due to variable typo in process_file (second_last_sep_overall_idx vs second_last_sep_idx_overall).
# Modification: Added onerror handler for os.walk to improve robustness in directory scanning.
# Modification (User Request): Changed unique credential storage to use (url, user, pass) tuples for the in-memory unique_lines set.

import os
# import mmap # Still imported, but not used in process_file after v3.1.2 reversion for line-by-line processing
import time
import sys
import threading
import logging
import signal
import uuid
import socket
import argparse
import errno
import re # Import regex module if needed (not currently using complex regex for keyword matching)
import base64  # For decoding Burp Suite responses
from queue import Queue, Empty
from itertools import permutations
# Keep msvcrt import for potential Windows usage, handle ImportError gracefully
try:
    import msvcrt
except ImportError:
    msvcrt = None # Define msvcrt as None if import fails

import json
from typing import Set, Dict, Any, List, Optional, Tuple # Added Tuple
from tqdm import tqdm
from datetime import datetime

# --- CONFIGURATION ---
APP_NAME = "UltraOptimizedKeywordExtractor"
APP_VERSION = "3.1.10" # Current version

# Default directories/files
BASE_OUTPUT_DIR = './output'
LOG_DIR = './logs'
WORDPRESS_OUTPUT_FILE = os.path.join(BASE_OUTPUT_DIR, 'wordpress.txt')

# --- NEW CONSTANTS AND HELPERS FOR CMS LOGIN NORMALISATION ---
# In addition to extracting credentials, the script can now normalise URLs to
# the appropriate login endpoint for a variety of CMS platforms.  It also
# collects the base installation path for WordPress sites so that a simple
# list of affected WordPress domains can be written out at the end of a run.

# Output file for unique WordPress base URLs (including subfolders).  Each
# entry contains only the scheme, host and any subfolder where WordPress is
# installed, always ending with a trailing slash.  Example lines:
#   https://example.com/
#   https://example.com/blog/
WORDPRESS_DOMAIN_FILE = os.path.join(BASE_OUTPUT_DIR, 'wordpress_domain.txt')

# Global set to accumulate unique WordPress base URLs during processing.  The
# final contents of this set are written to WORDPRESS_DOMAIN_FILE after all
# input files have been handled.  This is separate from credential storage
# because only the installation path is needed, not the username or password.
wordpress_domains_set: Set[str] = set()

def get_login_url(url: str) -> str:
    """
    Given an arbitrary URL extracted from a credential dump, attempt to
    construct the canonical login URL for a recognised CMS.  The function
    preserves the original scheme and host, normalises paths, strips query
    parameters and fragments, and appends the appropriate login script or
    route.  If no CMS patterns match, the original URL is returned unchanged.

    Parameters
    ----------
    url : str
        The raw URL extracted from input.

    Returns
    -------
    str
        A URL pointing directly to the CMS login page where a user would
        normally authenticate.
    """
    if not url:
        return url
    try:
        # Strip any query string or fragment to simplify pattern matching
        no_fragment = url.split('#', 1)[0]
        no_query = no_fragment.split('?', 1)[0]
        url = no_query
    except Exception:
        pass

    url_lower = url.lower()

    # Helper to build a login URL given a base and a relative path
    def build(base: str, path: str) -> str:
        if not base.endswith('/'):
            base = base + '/'
        return base + path.lstrip('/')

    # WordPress: detect any /wp- pattern and normalise to wp-login.php
    wp_match = re.search(r'/wp-(?:admin|login)', url_lower)
    if wp_match:
        idx = wp_match.start()
        base = url[:idx]
        return build(base, 'wp-login.php')
    # Specific WordPress install script
    if '/wp-admin/install.php' in url_lower:
        idx = url_lower.find('/wp-admin/install.php')
        base = url[:idx]
        return build(base, 'wp-login.php')

    # Joomla: use the administrator interface for login
    if '/administrator' in url_lower:
        idx = url_lower.find('/administrator')
        base = url[:idx]
        return build(base, 'administrator/index.php')
    if '/joomla' in url_lower:
        idx = url_lower.find('/joomla') + len('/joomla')
        base = url[:idx]
        return build(base, 'administrator/index.php')

    # Drupal: user login route
    if '/user/login' in url_lower:
        idx = url_lower.find('/user/login')
        base = url[:idx]
        return build(base, 'user/login')
    if '/drupal' in url_lower:
        idx = url_lower.find('/drupal') + len('/drupal')
        base = url[:idx]
        return build(base, 'user/login')

    # Moodle: login route
    if '/login/index.php' in url_lower:
        idx = url_lower.find('/login/index.php')
        base = url[:idx]
        return build(base, 'login/index.php')
    if '/moodle' in url_lower:
        idx = url_lower.find('/moodle') + len('/moodle')
        base = url[:idx]
        return build(base, 'login/index.php')

    # Magento: admin route
    if '/index.php/admin' in url_lower:
        idx = url_lower.find('/index.php/admin')
        base = url[:idx]
        return build(base, 'index.php/admin')
    if '/admin' in url_lower:
        idx = url_lower.find('/admin')
        base = url[:idx]
        return build(base, 'admin')
    if '/magento' in url_lower:
        idx = url_lower.find('/magento') + len('/magento')
        base = url[:idx]
        return build(base, 'admin')

    # PopojiCMS: admin route
    if '/po-admin' in url_lower:
        idx = url_lower.find('/po-admin')
        base = url[:idx]
        return build(base, 'po-admin')
    if '/popojicms' in url_lower:
        idx = url_lower.find('/popojicms') + len('/popojicms')
        base = url[:idx]
        return build(base, 'po-admin')

    # Laravel: common login path
    if '/login' in url_lower:
        idx = url_lower.find('/login')
        base = url[:idx]
        return build(base, 'login')
    if '/laravel' in url_lower:
        idx = url_lower.find('/laravel') + len('/laravel')
        base = url[:idx]
        return build(base, 'login')

    # CodeIgniter: typical login controller
    if '/index.php/login' in url_lower:
        idx = url_lower.find('/index.php/login')
        base = url[:idx]
        return build(base, 'index.php/login')
    if '/codeigniter' in url_lower:
        idx = url_lower.find('/codeigniter') + len('/codeigniter')
        base = url[:idx]
        return build(base, 'index.php/login')
    if '/ci' in url_lower:
        idx = url_lower.find('/ci') + len('/ci')
        base = url[:idx]
        return build(base, 'index.php/login')

    # OJS (Open Journal Systems): login route is often under index.php/login
    if '/index.php/index' in url_lower:
        idx = url_lower.find('/index.php/index')
        base = url[:idx]
        return build(base, 'index.php/index/login')
    for pattern in ['/openjournal', '/ojs', '/journals']:
        if pattern in url_lower:
            idx = url_lower.find(pattern) + len(pattern)
            base = url[:idx]
            return build(base, 'index.php/login')

    # OwnCloud: login route typically at index.php/login
    if '/index.php/login' in url_lower:
        idx = url_lower.find('/index.php/login')
        base = url[:idx]
        return build(base, 'index.php/login')
    if '/owncloud' in url_lower:
        idx = url_lower.find('/owncloud') + len('/owncloud')
        base = url[:idx]
        return build(base, 'index.php/login')

    # Generic heuristics: attempt to normalise /administrator, /admin or /login paths
    for pat in ['/administrator', '/admin', '/login', '/user/login']:
        if pat in url_lower:
            idx = url_lower.find(pat)
            base = url[:idx]
            # Remove leading slash from pat to avoid double slash
            return build(base, pat.lstrip('/'))

    # Default: return original URL if no pattern matched
    return url

def extract_wordpress_base(url: str) -> Optional[str]:
    """
    Extract the base installation path of a WordPress site from a given URL.
    The returned value includes the scheme, host and any subfolder where
    WordPress is installed, always ending with a trailing slash.  If the URL
    does not point to a WordPress login or admin path, ``None`` is returned.

    Examples
    --------
    >>> extract_wordpress_base('https://example.com/wp-login.php')
    'https://example.com/'
    >>> extract_wordpress_base('https://example.com/blog/wp-admin/install.php')
    'https://example.com/blog/'
    """
    if not url:
        return None
    url_lower = url.lower()
    # Identify the position of any wp- prefix
    wp_match = re.search(r'/wp-(?:admin|login)', url_lower)
    if not wp_match:
        return None
    idx = wp_match.start()
    base = url[:idx]
    if not base.endswith('/'):
        base = base + '/'
    return base

def parse_output_line(line: str) -> Optional[Tuple[str, str, str]]:
    """
    Parse a line from an output or CMS-specific file into its constituent
    components ``(url, user, pass)``.  The new output format uses ``#`` to
    separate the URL from the username and ``@`` to separate the username
    from the password.  Lines not conforming to this format are ignored.

    Parameters
    ----------
    line : str
        A single line from an output file.

    Returns
    -------
    Optional[Tuple[str, str, str]]
        A tuple containing URL, username and password, or ``None`` if the
        line cannot be parsed.
    """
    if not line:
        return None
    s = line.strip()
    if not s or '#' not in s or '@' not in s:
        return None
    try:
        url_part, rest = s.split('#', 1)
        user_part, pass_part = rest.split('@', 1)
        return url_part, user_part, pass_part
    except Exception:
        return None
OUTPUT_FILE_TEMPLATE = 'filtered_{instance_id}.txt'
PROCESSED_FILES_LOG_TEMPLATE = 'processed_files_{instance_id}.log'
ERROR_LOG_TEMPLATE = 'extractor_errors_{instance_id}.log'
DEFAULT_INPUT_DIR = r'./input'
LOCK_FILE = os.path.join(LOG_DIR, '.lock')

# --- NEW CONSTANTS AND HELPERS FOR CHUNKED OUTPUT ---
# To satisfy the requirement of splitting the output into ~100MB chunks, we define a
# maximum output file size (in bytes). When this threshold is exceeded, a new
# output file will be opened automatically. The naming convention preserves the
# original filename for the first chunk and appends a numeric suffix (e.g.
# `_2`, `_3`, …) for subsequent chunks. This logic is encapsulated in the
# `ChunkedWriter` class defined below.

MAX_OUTPUT_FILE_SIZE_BYTES: int = 100 * 1024 * 1024  # 100MB per output file chunk

from typing import IO  # for type hints with file-like objects

class ChunkedWriter:
    """A thin wrapper around a regular file handle that automatically
    rotates the underlying file when it grows beyond a configured size.

    The first file is created using the provided base path. Subsequent
    chunks append an underscore and an incrementing integer before the
    extension. For example, if the base path is `filtered_xyz.txt`, the
    sequence of chunks will be:

        filtered_xyz.txt (first chunk)
        filtered_xyz_2.txt (second chunk)
        filtered_xyz_3.txt (third chunk)
        ... and so on.

    The class exposes a minimal file-like interface (`write`, `flush`,
    `close`, and `closed` property) so it can be used as a drop-in
    replacement for a normal file handle. It maintains a list of all
    chunk paths created, which can be accessed via the `chunk_paths`
    attribute for final deduplication or merging.
    """
    def __init__(self, base_path: str, max_bytes: int, start_index: int = 1) -> None:
        self.base_path = base_path
        self.max_bytes = max_bytes
        # Track the current chunk index (1-based). Index 1 uses the base_path as-is.
        # Allow specifying a starting chunk index for resuming from an existing run.
        self._chunk_index = max(start_index, 1)
        # Internal list of created chunk file paths for later processing.
        self.chunk_paths: List[str] = []
        # Prepare the list of previous chunk filenames if starting index > 1.
        base_no_ext, ext = os.path.splitext(self.base_path)
        if self._chunk_index > 1:
            # Add paths for chunks 1 through start_index-1
            for i in range(1, self._chunk_index):
                if i == 1:
                    prev_path = self.base_path
                else:
                    prev_path = f"{base_no_ext}_{i}{ext}"
                self.chunk_paths.append(prev_path)
        # Open the current (resumed) chunk.
        self.current_path, self._file = self._open_chunk(self._chunk_index)
        # Add the current chunk path to the list
        self.chunk_paths.append(self.current_path)

    def _open_chunk(self, index: int) -> Tuple[str, IO[str]]:
        """Open a file for the given chunk index and return its path and handle."""
        base_no_ext, ext = os.path.splitext(self.base_path)
        if index == 1:
            path = self.base_path
        else:
            path = f"{base_no_ext}_{index}{ext}"
        # Ensure parent directories exist
        os.makedirs(os.path.dirname(path), exist_ok=True)
        fh = open(path, 'a', encoding='utf-8', newline='\n', errors='replace')
        return path, fh

    def _rotate_if_needed(self) -> None:
        """Check the size of the current file and rotate to a new one if needed."""
        try:
            current_size = os.path.getsize(self.current_path)
        except Exception:
            current_size = 0
        # Rotate only after the file exceeds the threshold; this may slightly
        # exceed the limit by the size of the last write, but avoids an
        # expensive per-line pre-check and keeps the implementation simple.
        if current_size >= self.max_bytes:
            # Close the existing file handle
            try:
                self._file.close()
            except Exception:
                pass
            # Increment the chunk index and open a new file
            self._chunk_index += 1
            self.current_path, self._file = self._open_chunk(self._chunk_index)
            self.chunk_paths.append(self.current_path)

    def write(self, text: str) -> None:
        """Write text to the current file and rotate if it grows too large."""
        # Perform the actual write
        self._file.write(text)
        # Flush to ensure file size reflects the latest write for an accurate size check
        try:
            self._file.flush()
        except Exception:
            pass
        # Check if we need to rotate to the next chunk
        self._rotate_if_needed()

    def flush(self) -> None:
        """Flush the underlying file buffer."""
        try:
            self._file.flush()
        except Exception:
            pass

    def close(self) -> None:
        """Close the current file handle."""
        try:
            self._file.close()
        except Exception:
            pass

    @property
    def closed(self) -> bool:
        """Return True if the current file handle is closed."""
        return self._file.closed


# Instance identification
INSTANCE_ID = f"{socket.gethostname()}_{os.getpid()}_{uuid.uuid4().hex[:6]}"
wordpress_unique_credentials: Set[Tuple[str, str, str]] = set()



# --- Keyboard Input Setup ---
# Global variables for termios settings on POSIX
_termios_settings_fd = None
_termios_old_settings = None

def _enable_raw_input():
    """Enable raw input mode for POSIX TTY."""
    global _termios_settings_fd, _termios_old_settings
    if sys.stdin.isatty(): # Only if stdin is a TTY
        try:
            import termios
            import tty
            # Save original settings before changing
            _termios_settings_fd = sys.stdin.fileno()
            _termios_old_settings = termios.tcgetattr(_termios_settings_fd)
            # Set raw mode: c_lflag &= ~(ICANON | ECHO)
            tty.setraw(sys.stdin.fileno(), termios.TCSANOW)
            logging.debug("Raw input mode enabled for POSIX TTY.")
            return True # Indicate success
        except (ImportError, termios.error, IOError) as e: # Catch termios/IOError during setup
             logging.warning(f"Failed to enable raw input mode: {e}. Interactive skip may not work.")
             _termios_settings_fd = None # Reset to indicate setup failed
             _termios_old_settings = None # Reset to indicate setup failed
             return False # Indicate failure
    return False # Indicate not a TTY or import failed


def _restore_normal_input():
    """Restore original terminal settings for POSIX TTY."""
    global _termios_settings_fd, _termios_old_settings
    if _termios_settings_fd is not None and _termios_old_settings is not None and sys.stdin.isatty():
        try:
            import termios
            # Restore original settings
            termios.tcsetattr(_termios_settings_fd, termios.TCSADRAIN, _termios_old_settings)
            logging.debug("Restored normal input mode for POSIX TTY.")
        except (ImportError, termios.error, IOError) as e: # Catch termios/IOError during restore
             logging.warning(f"Failed to restore terminal settings: {e}. Manual reset may be needed.")
        finally:
             _termios_settings_fd = None
             _termios_old_settings = None


# Register cleanup for termios settings on exit
# This helps ensure terminal is reset even if the program crashes or is interrupted
import atexit
atexit.register(_restore_normal_input)

# Define fallback functions first
_kbhit_fallback = lambda: False
_getch_fallback = lambda: b''

# Define _kbhit and _getch based on platform and availability
_kbhit = _kbhit_fallback # Default to fallback
_getch = _getch_fallback # Default to fallback
_has_working_kb_input = False # Flag to indicate if keyboard input is expected to work

if msvcrt is not None: # Windows
    _kbhit = msvcrt.kbhit
    _getch = msvcrt.getch
    _has_working_kb_input = True
    logging.debug("Using msvcrt for keyboard input.")
elif sys.platform != 'win32': # POSIX-like
    try:
        import select
        import termios # Check if termios is importable here too
        import tty     # Check if tty is importable here too

        def _kbhit_posix():
            if not sys.stdin.isatty(): return False
            # Check if there's anything to read without blocking
            dr, _, _ = select.select([sys.stdin], [], [], 0)
            return dr != []

        def _getch_posix():
             # This function assumes raw mode is handled by the input_listener_thread's try/finally
             # If called outside that context, it might need _enable_raw_input() which might mess up terminal state if not managed.
             if not sys.stdin.isatty(): return b''
             try:
                # Use select to wait for data with a small timeout, then read
                i, _, _ = select.select([sys.stdin], [], [], 0.01) # 10ms timeout
                if i:
                    ch = sys.stdin.read(1)
                    # Return as bytes using the terminal's encoding
                    return ch.encode(sys.stdin.encoding, errors='replace') if ch else b''
                return b'' # No data available within timeout
             except Exception as e:
                logging.debug(f"_getch_posix read error: {e}", exc_info=True)
                return b'' # Return empty bytes on error

        _kbhit = _kbhit_posix
        _getch = _getch_posix
        _has_working_kb_input = True # Assume working if imports succeed
        logging.debug("Using termios/select for keyboard input.")

    except (ImportError, AttributeError, IOError) as e: # Catch import or file descriptor issues
        # If any of these modules/attributes aren't available, keyboard input won't work correctly
        logging.warning(f"Non-Windows keyboard input modules (termios/tty/select) not fully available or failed to initialize ({e}). Interactive skip will be non-functional.")
        _kbhit = _kbhit_fallback
        _getch = _getch_fallback
        _has_working_kb_input = False
else: # Fallback for unknown platform or errors during initial checks
    logging.warning("Keyboard input modules not available. Interactive skip will be non-functional.")
    _kbhit = _kbhit_fallback
    _getch = _getch_fallback
    _has_working_kb_input = False


# --- File Locking Utility ---
class FileLock:
    def __init__(self, lock_file, timeout=10, delay=0.1): # Added default timeout/delay to constructor if needed elsewhere
        self.lock_file = lock_file
        self.lock_handle = None
        # Store timeout and delay if they are to be used consistently by acquire
        self.timeout = timeout
        self.delay = delay

    def acquire(self, timeout=None, delay=None): # Allow overriding constructor defaults
        # Use method-specific timeout/delay if provided, else use instance defaults
        _timeout = timeout if timeout is not None else self.timeout
        _delay = delay if delay is not None else self.delay

        start_time = time.time()
        os.makedirs(os.path.dirname(self.lock_file), exist_ok=True)
        logging.debug(f"Attempting to acquire lock: {self.lock_file}")
        while True:
            try:
                if sys.platform == 'win32':
                    mode = os.O_CREAT | os.O_EXCL | os.O_WRONLY | getattr(os, 'O_TEMPORARY', 0) | getattr(os, 'O_NOINHERIT', 0)
                    fd = os.open(self.lock_file, mode)
                    self.lock_handle = os.fdopen(fd, 'w', encoding='utf-8')
                else: # POSIX-like systems
                    import fcntl
                    self.lock_handle = open(self.lock_file, 'w', encoding='utf-8')
                    fcntl.flock(self.lock_handle, fcntl.LOCK_EX | fcntl.LOCK_NB)

                self.lock_handle.write(f"{os.getpid()}\n{INSTANCE_ID}\n{time.time()}"); self.lock_handle.flush()
                logging.debug(f"Lock acquired: {self.lock_file}")
                return True
            except (IOError, OSError) as e:
                if sys.platform == 'win32' and hasattr(e, 'winerror') and e.winerror in (183, 32): # ERROR_ALREADY_EXISTS, ERROR_SHARING_VIOLATION
                    pass
                elif sys.platform != 'win32' and hasattr(e, 'errno') and e.errno in (errno.EAGAIN, errno.EACCES, errno.EWOULDBLOCK):
                    pass
                elif hasattr(e, 'errno') and e.errno == errno.EEXIST: # Should be caught by O_EXCL on Win, but good for general
                    pass
                else:
                    logging.error(f"Unexpected error acquiring lock {self.lock_file}: {e}", exc_info=True)
                    raise # Reraise unexpected errors

                if self.lock_handle: # Ensure handle is closed if lock acquisition failed mid-way
                    try: self.lock_handle.close()
                    except Exception as close_e: logging.debug(f"Error closing handle after failed lock acquire: {close_e}")
                    self.lock_handle = None

                if _timeout is not None and time.time() - start_time > _timeout:
                    logging.debug(f"Lock acquisition timed out: {self.lock_file}")
                    return False
                time.sleep(_delay)

    def release(self):
        """Release the file lock and attempt to remove the lock file from the filesystem."""
        if self.lock_handle:
            logging.debug(f"Attempting to release lock: {self.lock_file}")
            try:
                try:
                    self.lock_handle.close()
                except Exception as e: # Catch any error during close
                    logging.debug(f"Error closing lock file handle during release: {e}")
                self.lock_handle = None # Important to set to None even if close failed
                # Attempt removal only after handle is confirmed closed or was never properly opened.
                os.remove(self.lock_file)
                logging.debug(f"Lock file removed: {self.lock_file}")
            except OSError as e:
                 if hasattr(e, 'errno') and e.errno == errno.ENOENT: # FileNotFoundError subclass
                      logging.debug(f"Lock file already gone during removal attempt: {self.lock_file}")
                      pass # It's okay if it's already gone
                 else:
                    # This might happen if another process acquired and removed it quickly, or permissions issue
                    logging.warning(f"Error removing lock file {self.lock_file}: {e}")
            except Exception as e: # Catch any other unexpected error
                 logging.warning(f"Unexpected error during lock file removal {self.lock_file}: {e}")

    def __enter__(self):
        if not self.acquire():
             # Consider a more specific exception if desired
             raise RuntimeError(f"Failed to acquire file lock within timeout: {self.lock_file}")
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()

# --- TQDM Logging Handler ---
class TqdmLoggingHandler(logging.Handler):
    def __init__(self, level=logging.NOTSET):
        super().__init__(level)
        self.stream = sys.stdout # Default to stdout

    def emit(self, record):
        # Check if tqdm is available and we are in a TTY environment suitable for tqdm.write
        if 'tqdm' in sys.modules and hasattr(tqdm, 'write') and self.stream.isatty():
            try:
                 msg = self.format(record)
                 tqdm.write(msg, file=self.stream) # Use the stored stream
                 self.flush()
            except Exception as e: # Fallback if tqdm.write fails for some reason
                 self.stream.write(f"Error using tqdm.write: {e} - Falling back to standard print.\n")
                 self.stream.write(self.format(record) + '\n')
                 self.stream.flush()
        else: # Fallback for non-TTY or if tqdm is not fully functional
            self.stream.write(self.format(record) + '\n')
            self.stream.flush()

    def flush(self):
        # Ensure the stream has a flush method before calling it
        if hasattr(self.stream, 'flush'):
            self.stream.flush()

# --- Setup Logging ---
def setup_logging(output_dir: str, error_log_file: str, level=logging.INFO):
    os.makedirs(output_dir, exist_ok=True) # Ensure output directory exists
    log_formatter = logging.Formatter(f'%(asctime)s [%(levelname)-8s] [Instance: {INSTANCE_ID[:8]}] - %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
    root_logger = logging.getLogger()
    root_logger.setLevel(level) # Set level on root logger

    # Remove existing handlers to prevent duplicate logging if setup_logging is called multiple times
    if root_logger.hasHandlers():
        for handler in list(root_logger.handlers): # Iterate over a copy
            try:
                handler.close()
            except Exception as e:
                logging.debug(f"Error closing old log handler: {e}")
            root_logger.removeHandler(handler)
    logging.debug("Old logging handlers removed from root logger.")

    # Error File Handler (logs ERROR and CRITICAL messages)
    try:
        error_file_path = os.path.join(output_dir, error_log_file)
        error_handler = logging.FileHandler(error_file_path, mode='a', encoding='utf-8')
        error_handler.setFormatter(log_formatter)
        error_handler.setLevel(logging.ERROR) # Only log errors and above to this file
        root_logger.addHandler(error_handler)
        logging.debug(f"Error log file handler added: {error_file_path} (Level: ERROR)")
    except Exception as e:
         # If error handler fails, log to a potentially available console and then try to raise
         logging.error(f"Failed to create error log file handler for '{error_log_file}': {e}")
         # Depending on severity, you might want to raise an error here or exit

    # Console Handler (uses TqdmLoggingHandler if TTY, otherwise standard StreamHandler)
    if sys.stdout.isatty(): # Check if output is to a TTY
         console_handler = TqdmLoggingHandler()
         console_handler.setFormatter(log_formatter)
         console_handler.setLevel(level) # Use the general log level
         root_logger.addHandler(console_handler)
         logging.debug("Console handler added (attempted TqdmLoggingHandler) (TTY detected).")
    else:
         # Standard stream handler for non-TTY environments (e.g., piped output, cron jobs)
         console_handler = logging.StreamHandler(sys.stdout)
         console_handler.setFormatter(log_formatter)
         console_handler.setLevel(level) # Use the general log level
         root_logger.addHandler(console_handler)
         logging.debug("Standard StreamHandler used for console output (non-TTY detected).")

    # Initial log messages
    logging.info(f"{APP_NAME} v{APP_VERSION} - Extraction started")
    logging.info(f"Instance ID: {INSTANCE_ID}")
    logging.info(f"Output directory: {os.path.abspath(output_dir)}")
    logging.info(f"Log level set to: {logging.getLevelName(level)}")


# --- Validation Functions ---
def is_valid_url_part(s: str) -> bool:
    """
    Validate that a string resembles a usable URL part (e.g., a domain with an optional path).

    This helper performs a series of heuristic checks to filter out obvious non-URL values.
    Importantly, it strips common wrappers and removes any scheme (``http://`` or ``https://``)
    prior to extracting the domain for top‑level domain (TLD) validation. Without removing
    the scheme, a path such as ``https://mysite.com/path`` would incorrectly yield
    ``https:`` as the domain and fail TLD checks. After these normalisations, the function
    verifies that the value contains at least one period, does not contain spaces or
    backslashes, is not simply a number, contains at least one alphabetic character and
    terminates in a plausible TLD of 2–10 alphabetic characters.

    :param s: The candidate string representing a URL (or partial URL).
    :return: True if ``s`` passes heuristic URL validation; False otherwise.
    """
    if not s:
        return False
    # Remove wrapping characters that sometimes surround a URL in log files
    s = s.strip('"/\\()[]')
    if not s:
        return False
    # Reject strings containing whitespace or backslashes (unlikely in a URL)
    if ' ' in s or '\\' in s:
        return False
    # Ensure there is at least one dot somewhere (e.g., domain.tld)
    if '.' not in s:
        return False
    # Disallow values that look like e‑mail addresses (contain '@' but no path)
    if '@' in s and '/' not in s:
        return False
    # Disallow values that are purely numeric (with at most one dot)
    if s.replace('.', '', 1).isdigit():
        return False
    # Must contain at least one alphabetic character
    if not any(c.isalpha() for c in s):
        return False
    # Strip any scheme prefix (e.g., http:// or https://) to isolate the domain
    # We only remove the scheme; the remainder retains any path component.
    try:
        s_no_scheme = re.sub(r'^[a-zA-Z]+://', '', s)
    except Exception:
        s_no_scheme = s
    # Extract the domain by taking everything before the first '/'
    domain_part = s_no_scheme.split('/')[0] if s_no_scheme else ''
    # Validate a plausible TLD on the domain
    try:
        parts = domain_part.split('.')
        if len(parts) < 2:
            return False
        tld = parts[-1]
        # TLD should be 2‑10 alphabetic characters
        if not (2 <= len(tld) <= 10 and tld.isalpha()):
            return False
    except Exception:
        return False
    return True

def is_valid_user_part(user_string: str) -> bool:
    if not user_string: # Must not be empty
        return False
    # Minimum length for a username might be application-specific.
    # This was 3 in some contexts, 5 here. Let's keep 5 as per last known.
    min_user_len = 5
    if len(user_string) < min_user_len:
        return False
    # Could add checks for invalid characters if known.
    return True

def is_valid_pass_part(pass_string: str) -> bool:
    if not pass_string: # Must not be empty
        return False
    # Reject common placeholder or weak passwords.
    # Case-sensitive comparison for these.
    if pass_string == '[UNKNOWNorV70]' or pass_string == '[N/A]' or pass_string == '123456':
        return False
    # Minimum password length.
    min_pass_len = 4 # Adjusted from 6, or keep 6 if that's the true minimum desired. Let's use 4 as per v3.1.9
    if len(pass_string) < min_pass_len:
        return False
    return True


def is_wordpress_url(url: str) -> bool:
    """
    Detects if a URL is likely a WordPress site using fast, non-intrusive methods.
    """
    # Enhanced regex for broader matching, case-insensitive
    wp_regex = re.compile(r'/wp-(login|admin)', re.IGNORECASE)
    if wp_regex.search(url):
        return True
    
    # Fallback for simple patterns
    url_lower = url.lower()
    wp_patterns = ['/wp-login', 'wp-login.php', '/wp-admin', 'wp-admin/install.php']
    if any(pattern in url_lower for pattern in wp_patterns):
        return True
        
    return False

# -----------------------------------------------------------------------------
# CMS Detection Helpers
#
# Many web applications in Indonesia's government and university domains run on
# a variety of content management systems (CMS) or frameworks. To categorize
# extracted credentials by the underlying platform, we define a mapping of CMS
# names to simple substring patterns. These patterns are heuristics drawn
# from typical URL structures (e.g. login or admin paths) and CMS-specific
# identifiers. They are not exhaustive but should cover the most common cases.

# Patterns used to detect various CMS/frameworks. Each entry maps a lowercased
# CMS identifier (used in filenames) to a list of substrings that, if
# present in a URL (case-insensitive), suggest the site is built on that CMS.
CMS_PATTERN_MAP: Dict[str, List[str]] = {
    # Joomla detection: typical admin area path, component query string and explicit mention
    'joomla': [
        '/administrator/index.php',    # admin entry point
        '/administrator/login',        # admin login path
        '/joomla',                     # explicit mention of CMS name
        'index.php?option=com',        # component parameter used by Joomla extensions
        'index.php?option=login',      # login option pattern
    ],
    # Open Journal Systems (OJS) detection: journal‐related paths
    'ojs': [
        '/ojs',                        # explicit OJS mention
        '/openjournal',                # alternative naming pattern
        '/journals',                   # plural variant (commonly used by OJS)
        '/public/journals',            # public resource path
        '/index.php/index',            # OJS index route
        '/index.php/journal',          # explicit journal route
    ],
    # Moodle detection: login/course paths and the moodle directory itself
    'moodle': [
        '/moodle',                    # base directory when installed as subfolder
        '/login/index.php',           # login route
        '/course/view.php',           # course page
        '/user/profile.php',          # user profile page
        '/my',                        # user dashboard
    ],
    # Laravel detection: directories unique to Laravel structure
    'laravel': [
        '/laravel',                   # explicit mention of framework
        '/public/index.php',          # typical front controller
        '/public/storage',            # storage symlink within public
        '/storage/app',               # storage path
        '/vendor/laravel',            # vendor folder containing Laravel framework
        '/resources/views',           # resources folder specific to Laravel
        '/artisan',                   # CLI script; presence hints at Laravel
    ],
    # CodeIgniter detection: patterns associated with its structure
    'codeigniter': [
        '/codeigniter',               # explicit mention
        '/ci',                        # abbreviation sometimes used
        '/system/core',               # core system directory
        '/application/config',        # config path
        '/welcome_message',           # default welcome controller generated by CI
        '/index.php/login',           # login controller pattern (more specific than bare index.php)
        '/index.php/admin',           # admin controller pattern
        '/index.php/user',            # user controller pattern
        # Note: we deliberately omit the generic '/index.php' because many PHP
        # applications (including Joomla and others) route through index.php,
        # which led to false positives.  Including only CI‑specific paths
        # reduces spurious matches while still matching common CI routes.
    ],
    # Drupal detection: nodes, user login and other core paths
    'drupal': [
        '/drupal',                    # explicit mention
        '/user/login',                # login route
        '/node/',                     # node paths for content
        '/sites/all',                 # contributed modules/themes
        '/modules',                   # modules directory
        '/themes',                    # themes directory
    ],
    # Magento detection: shopping/cart/product paths and explicit mention
    'magento': [
        '/magento',                   # explicit mention
        '/checkout/cart',             # cart path
        '/catalog/product',           # product listing path
        '/index.php/admin',           # admin login for Magento 1
        '/customer/account/login',    # customer login
    ],
    # PopojiCMS detection: admin/content/theme folders
    'popojicms': [
        '/popojicms',                 # explicit mention
        '/po-admin',                  # admin directory
        '/po-content',                # content directory
        '/po-theme',                  # theme directory
    ],

    # OwnCloud detection: common paths and endpoints
    # These patterns follow the same heuristic style as other CMS entries.
    # We include the base installation folder, remote API paths, and ocs API
    # endpoints which are specific to OwnCloud.  The list is intentionally
    # conservative to minimise false positives on generic PHP applications.
    'owncloud': [
        '/owncloud',        # explicit installation path or subfolder
        '/remote.php',      # remote DAV/WebDAV/CalDAV endpoints
        '/status.php',      # status endpoint used by OwnCloud
        '/ocs/v1.php',      # OCS API version 1
        '/ocs/v2.php',      # OCS API version 2
    ],
}

# Directory names for CMS output (for neat modular structure)
# These mappings translate internal CMS identifiers to user-friendly
# folder/file names used when writing per‑CMS outputs. Keys not present
# default to themselves.
CMS_DIR_MAP: Dict[str, str] = {
    'owncloud': 'owncloud',
    'wordpress': 'wordpress',
    'moodle': 'moodle',
    'ojs': 'ojs',
    'laravel': 'laravel',
    'codeigniter': 'codeigniter',
    'drupal': 'drupal',
    'opensid': 'opensid',
    'joomla': 'joomla',
    'popojicms': 'popoji-cms',
}

# -----------------------------------------------------------------------------
# HTTP CMS Detection Heuristics
#
# To extend the detection capabilities beyond simple URL pattern matching, we
# analyze full HTTP request/response pairs exported from tools like Burp
# Suite.  Each entry in this mapping defines heuristics based on three
# categories:
#   * path patterns: substrings in the request path that are indicative of
#       the CMS (e.g. `/wp-` for WordPress, `/administrator` for Joomla).
#   * cookie names: session cookie names that are set by the CMS (e.g.
#       `MoodleSession`, `laravel_session`).  Matching cookie names carry
#       significant weight because they are rarely reused across different
#       frameworks.
#   * body patterns: substrings found within the HTML body of the response
#       (e.g. `wp-content`, `Open Journal Systems`).  These patterns are
#       generally case-insensitive.  Body patterns should be used in
#       conjunction with other signals because many generic terms (like
#       `login`) appear across multiple platforms.
#
# The scoring function (see detect_cms_from_http_item) uses these patterns to
# accumulate evidence for each CMS.  A match in the cookie list is treated as
# a strong indicator.  Multiple weak indicators (such as path+body) can also
# confirm a CMS.  These heuristics are intentionally conservative to
# reduce false positives when processing generic or unrelated HTTP traffic.
#
HTTP_CMS_PATTERNS: Dict[str, Dict[str, List[str]]] = {
    'wordpress': {
        'path': [
            '/wp-',           # common directory prefix for WordPress
            '/wp-login',      # explicit login script
            '/wp-admin',      # admin dashboard
        ],
        'cookies': [
            'wordpress_logged_in',
            'wordpress_sec',
            'wp-settings',
            'wp_lang',
        ],
        'body': [
            'wp-content',
            'wordpress',
            'wp-login',
            'wp-admin',
        ],
    },
    'joomla': {
        'path': [
            '/administrator',              # Joomla admin folder
            '/index.php?option=com',       # component query parameter
            '/joomla',                     # explicit mention of Joomla
        ],
        'cookies': [
            'joomla',                      # cookie prefixes often include the CMS name
        ],
        'body': [
            'joomla',
        ],
    },
    'moodle': {
        'path': [
            '/moodle',                    # base directory
            '/login/index.php',           # login route
            '/course/view.php',           # course page
            '/user/profile.php',          # user profile
            '/my',                        # dashboard
        ],
        'cookies': [
            'moodlesession',
            'moodlesessiontest',
        ],
        'body': [
            'moodle',
        ],
    },
    'owncloud': {
        'path': [
            '/owncloud',                  # installation path
        ],
        'cookies': [
            'oc_sessionpassphrase',
            'oc_token',
            'oc_session',
        ],
        'body': [
            'owncloud',
            'oc-core',
        ],
    },
    'ojs': {
        'path': [
            '/ojs',                        # explicit mention
            '/index.php/index',            # OJS index route
            '/index.php/journal',          # journal route
            '/journals',                   # plural variant
        ],
        'cookies': [
            'ojssid',
        ],
        'body': [
            'open journal systems',
            'ojs',
        ],
    },
    'laravel': {
        'path': [
            '/laravel',                   # explicit mention
            '/public/index.php',          # front controller
            '/artisan',                   # CLI entry point
            '/storage/app',               # storage path
            '/vendor/laravel',            # vendor folder
        ],
        'cookies': [
            'laravel_session',
            'xsrf-token',
        ],
        'body': [
            'laravel',
            'csrf-token',
        ],
    },
    'codeigniter': {
        'path': [
            '/codeigniter',               # explicit mention
            '/welcome_message',           # default welcome controller
            '/index.php/login',           # login controller
            '/index.php/admin',           # admin controller
            '/index.php/user',            # user controller
        ],
        'cookies': [
            'ci_session',                 # session cookie name
        ],
        'body': [
            'codeigniter',
        ],
    },
}

# -----------------------------------------------------------------------------
# HTTP analysis helpers

def _decode_http_response(resp_elem: Any) -> Tuple[str, str]:
    """
    Given a <response> element from a Burp Suite HTTP history export, decode
    the base64 payload (if applicable) and split it into headers and body.

    Parameters
    ----------
    resp_elem : xml.etree.ElementTree.Element or compatible
        The <response> element from the Burp export.  Its text content is
        expected to contain the raw HTTP response with CRLF line endings.

    Returns
    -------
    Tuple[str, str]
        A tuple `(headers, body)` where headers is the header section (status
        line and all header fields) as a string and body is the response body
        as a string.  Both values are decoded using 'latin-1' with
        replacement of invalid characters to ensure robustness.
    """
    data_text = resp_elem.text or ''
    # Determine if the response is base64 encoded (attribute base64="true")
    is_b64 = False
    try:
        # Use .get() instead of direct indexing for safety
        is_b64 = str(resp_elem.attrib.get('base64', 'false')).lower() == 'true'
    except Exception:
        is_b64 = False

    try:
        raw_bytes: bytes
        if is_b64:
            # Burp exports responses as base64 when binary or non-text content
            raw_bytes = base64.b64decode(data_text)
        else:
            # If not base64, assume text and encode as latin-1
            raw_bytes = data_text.encode('latin-1', errors='replace')
    except Exception:
        # Fallback: treat response as empty if decoding fails
        return '', ''

    # Separate headers and body at the first occurrence of two consecutive CRLFs
    # According to RFCs, the sequence CRLF CRLF denotes the end of headers
    headers_bytes: bytes
    body_bytes: bytes
    try:
        if b"\r\n\r\n" in raw_bytes:
            headers_bytes, body_bytes = raw_bytes.split(b"\r\n\r\n", 1)
        elif b"\n\n" in raw_bytes:
            # Handle LF-only line endings as a fallback
            headers_bytes, body_bytes = raw_bytes.split(b"\n\n", 1)
        else:
            # No body found; treat entire response as headers
            headers_bytes, body_bytes = raw_bytes, b''
    except Exception:
        headers_bytes, body_bytes = raw_bytes, b''

    try:
        headers_str = headers_bytes.decode('latin-1', errors='replace')
    except Exception:
        headers_str = ''
    try:
        body_str = body_bytes.decode('latin-1', errors='replace')
    except Exception:
        body_str = ''
    return headers_str, body_str


def detect_cms_from_http_item(path: str, headers: str, body: str) -> List[str]:
    """
    Perform heuristic detection of Content Management Systems based on HTTP
    transaction data.  This function inspects the request path, response
    headers (including Set-Cookie), and response body for patterns defined in
    HTTP_CMS_PATTERNS.  It returns a list of CMS identifiers (keys from
    HTTP_CMS_PATTERNS) that are inferred from the data.

    Evidence is accumulated for each CMS; matching a cookie name is treated as
    a strong indicator.  A CMS is returned if either a cookie match is
    observed, or at least two different evidence types (e.g. path and body)
    match.  This reduces false positives from generic path or body strings.

    Parameters
    ----------
    path : str
        The request path (including query string) as recorded in the Burp
        history file.
    headers : str
        The HTTP response header section as a single string.  Headers are
        separated by CRLF sequences.
    body : str
        The HTTP response body as a string.

    Returns
    -------
    List[str]
        A list of detected CMS identifiers.  The list may contain multiple
        entries if evidence suggests more than one CMS, though this is
        uncommon.  When no CMS can be inferred, an empty list is returned.
    """
    matches: List[str] = []
    # Normalize inputs to lowercase for case-insensitive matching
    path_lower = (path or '').lower()
    headers_lower = (headers or '').lower()
    body_lower = (body or '').lower()

    # Extract cookie names from Set-Cookie headers
    cookie_names: List[str] = []
    for header_line in headers.split('\n'):
        # The header line may contain CR and LF; strip whitespace
        line = header_line.strip()
        if not line:
            continue
        # Check for 'Set-Cookie:' prefix (case-insensitive)
        if line.lower().startswith('set-cookie'):
            # Split at first ':' to separate header name and values
            try:
                _hdr, cookie_string = line.split(':', 1)
            except Exception:
                continue
            cookie_string = cookie_string.strip()
            # A Set-Cookie header can set multiple cookies separated by comma;
            # however, cookies themselves may contain commas in values.  To
            # simplify, we split on semicolon and equal sign to extract names.
            try:
                # The cookie name is before the first '=' character
                cookie_pair = cookie_string.split(';', 1)[0]
                cookie_name = cookie_pair.split('=', 1)[0].strip().lower()
                if cookie_name:
                    cookie_names.append(cookie_name)
            except Exception:
                continue

    # Evaluate each CMS pattern set
    for cms_key, patt in HTTP_CMS_PATTERNS.items():
        score = 0
        cookie_hit = False
        # Check path patterns
        for p in patt.get('path', []):
            if p and p.lower() in path_lower:
                score += 1
                break
        # Check cookie names; treat any cookie match as a strong indicator
        for cpat in patt.get('cookies', []):
            for cname in cookie_names:
                # Cookie patterns are substring-matched to allow prefixes
                if cpat.lower() in cname:
                    cookie_hit = True
                    break
            if cookie_hit:
                break
        if cookie_hit:
            score += 2  # Strong indicator adds two points
        # Check body patterns
        for bp in patt.get('body', []):
            if bp and bp.lower() in body_lower:
                score += 1
                break
        # Determine if evidence is sufficient
        #   - If cookie hit (score >= 2) then accept
        #   - Or if at least two evidence sources (score >= 2) then accept
        if score >= 2:
            matches.append(cms_key)

    return matches


def process_http_history_file(file_path: str, cms_records: Dict[str, List[str]], cms_counts: Dict[str, int]) -> None:
    """
    Parse a Burp Suite HTTP history XML file and update per-CMS detection
    records.  Each detected CMS occurrence results in an entry being added to
    `cms_records[cms]` and the corresponding count incremented in
    `cms_counts[cms]`.  This function is idempotent and does not return
    anything; results accumulate in the provided dictionaries.

    Parameters
    ----------
    file_path : str
        The path to the Burp Suite XML file to parse.
    cms_records : Dict[str, List[str]]
        A dictionary keyed by CMS identifier, mapping to a list of detection
        strings describing the evidence found for that CMS.
    cms_counts : Dict[str, int]
        A dictionary keyed by CMS identifier, mapping to a count of detections
        observed across all processed files.  This dictionary will be updated
        in-place.
    """
    try:
        import xml.etree.ElementTree as ET
    except Exception:
        logging.error(f"Failed to import ElementTree when parsing HTTP history file '{file_path}'.")
        return
    try:
        tree = ET.parse(file_path)
        root = tree.getroot()
    except Exception as e:
        logging.error(f"Error parsing XML file '{file_path}': {e}")
        return
    # Each <item> represents a single HTTP transaction
    items = root.findall('item') if root is not None else []
    if not items:
        logging.info(f"No <item> elements found in HTTP history file '{file_path}'.")
        return
    for item in items:
        try:
            url = item.findtext('url', default='').strip()
            path = item.findtext('path', default='').strip()
            resp_elem = item.find('response')
            if resp_elem is None:
                continue
            headers_str, body_str = _decode_http_response(resp_elem)
            detected = detect_cms_from_http_item(path, headers_str, body_str)
            if not detected:
                # Fallback: attempt detection using existing URL heuristics
                detected = detect_cms(url)
            if not detected:
                continue
            # Build evidence string for the record.  Include URL and reasons
            for cms_key in detected:
                # Assemble a simple reason summary: we record which evidence
                # types contributed.  This helps with traceability.
                reasons: List[str] = []
                plower = path.lower()
                hlower = headers_str.lower()
                blower = body_str.lower()
                # Check path patterns
                for p in HTTP_CMS_PATTERNS.get(cms_key, {}).get('path', []):
                    if p and p.lower() in plower:
                        reasons.append(f"path:{p}")
                        break
                # Check cookie patterns
                for cpat in HTTP_CMS_PATTERNS.get(cms_key, {}).get('cookies', []):
                    for c in hlower.split('\n'):
                        # Lowercase line for consistent comparison
                        line = c.strip().lower()
                        if not line:
                            continue
                        if line.startswith('set-cookie') and cpat.lower() in line:
                            reasons.append(f"cookie:{cpat}")
                            break
                    if any(r.startswith('cookie') for r in reasons):
                        break
                # Check body patterns
                for bp in HTTP_CMS_PATTERNS.get(cms_key, {}).get('body', []):
                    if bp and bp.lower() in blower:
                        reasons.append(f"body:{bp}")
                        break
                if not reasons:
                    # If none of the HTTP heuristics matched (e.g. fallback via detect_cms)
                    reasons.append('heuristic:url')
                # Construct record line
                record = f"{url} | {cms_key} | {', '.join(reasons)}"
                cms_records.setdefault(cms_key, []).append(record)
                cms_counts[cms_key] = cms_counts.get(cms_key, 0) + 1
        except Exception as e:
            logging.error(f"Error processing item in '{file_path}': {e}", exc_info=True)
            continue


def write_http_detection_results(cms_records: Dict[str, List[str]], cms_counts: Dict[str, int], base_output_dir: str) -> None:
    """
    Write the accumulated HTTP-based CMS detection results into a structured
    directory hierarchy.  For each CMS with detections, a subdirectory under
    `base_output_dir` is created (if it does not already exist) named after
    the CMS.  The file `results.txt` within each CMS directory contains one
    line per detection in the format "URL | cms | reason1, reason2, ...".

    Additionally, a `summary.txt` file is created in `base_output_dir` that
    lists each CMS along with the total number of detections observed.  A
    `log` subdirectory is also created and a `processing.log` file is
    appended to; during normal execution this logging is already handled by
    Python's logging module, so this function only ensures directories exist.

    Parameters
    ----------
    cms_records : Dict[str, List[str]]
        The dictionary of detection records keyed by CMS identifier.
    cms_counts : Dict[str, int]
        The dictionary of detection counts per CMS.
    base_output_dir : str
        The base directory under which the CMS-specific subdirectories should be
        created.
    """
    try:
        if not cms_records:
            # Nothing to write
            return
        # Ensure base directory exists.  This directory should represent
        # the root of CMS detection outputs (e.g. cms-detect).  Create
        # parent directories as needed.
        os.makedirs(base_output_dir, exist_ok=True)
        # Create a dedicated log directory at the same level as the CMS
        # output root.  For example, if base_output_dir is
        # '/path/to/cms-detect', logs will be written to '/path/to/log'.
        parent_dir = os.path.dirname(base_output_dir)
        log_dir = os.path.join(parent_dir, 'log')
        os.makedirs(log_dir, exist_ok=True)
        # Write per-CMS results
        for cms_key, records in cms_records.items():
            # Map internal CMS identifier to external directory name
            folder_name = CMS_DIR_MAP.get(cms_key, cms_key)
            cms_dir = os.path.join(base_output_dir, folder_name)
            os.makedirs(cms_dir, exist_ok=True)
            results_path = os.path.join(cms_dir, 'results.txt')
            # Write or append results
            try:
                with open(results_path, 'a', encoding='utf-8', errors='replace') as fh:
                    for rec in records:
                        fh.write(rec + '\n')
            except Exception as e:
                logging.error(f"Error writing results for CMS '{cms_key}' to '{results_path}': {e}")
        # Write summary file
        summary_path = os.path.join(base_output_dir, 'summary.txt')
        try:
            with open(summary_path, 'a', encoding='utf-8', errors='replace') as fh:
                timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                fh.write(f"Summary generated on {timestamp}\n")
                for cms_key, count in cms_counts.items():
                    fh.write(f"{cms_key}: {count}\n")
        except Exception as e:
            logging.error(f"Error writing summary file '{summary_path}': {e}")
        # Ensure log file exists; actual logging is handled globally
        log_file_path = os.path.join(log_dir, 'processing.log')
        try:
            # Touch the file to ensure it exists
            with open(log_file_path, 'a', encoding='utf-8'):
                pass
        except Exception:
            pass
    except Exception as outer_e:
        logging.error(f"Unexpected error while writing HTTP detection results: {outer_e}", exc_info=True)

# Unique credential stores for each CMS (including WordPress). These sets help
# prevent duplicate entries from being written to the per-CMS files across runs.
# WordPress is included explicitly even though its detection uses a separate
# helper (is_wordpress_url()).
cms_unique_credentials: Dict[str, Set[Tuple[str, str, str]]] = {
    **{cms: set() for cms in CMS_PATTERN_MAP.keys()},
    'wordpress': set(),
}

# Output file handles for each CMS (including WordPress) will be stored here
cms_output_files: Dict[str, Optional[Any]] = {
    **{cms: None for cms in CMS_PATTERN_MAP.keys()},
    'wordpress': None,
}

def detect_cms(url: str) -> List[str]:
    """
    Given a URL, returns a list of CMS identifiers (keys from CMS_PATTERN_MAP)
    that match the patterns defined. WordPress detection is handled separately
    using is_wordpress_url() to ensure robust detection of WordPress sites.
    """
    matches: List[str] = []
    url_lower = url.lower()
    # Check WordPress separately to leverage the existing heuristic
    if is_wordpress_url(url):
        matches.append('wordpress')
    # Check other CMS patterns
    for cms, patterns in CMS_PATTERN_MAP.items():
        for pattern in patterns:
            if pattern and pattern in url_lower:
                matches.append(cms)
                break  # avoid duplicate addition for the same CMS
    return matches

def parse_line_robust(line: str, *, _attempt_fallback: bool = True) -> Optional[Tuple[str, str, str]]:
    """
    Robustly parse a single line into a `(url, user, pass)` tuple.

    The parser handles JSON/JSONL objects as well as unstructured text containing a
    mixture of separators.  It normalises common delimiters to a single pipe
    character before attempting to identify the three fields.  A scoring
    heuristic is used to determine the best candidate triple among all
    permutations of extracted parts.  If initial parsing fails to produce a
    sufficiently confident match and fallback attempts are enabled, the parser
    will attempt specialised handling for dot- and dash-separated credentials
    commonly seen in certain datasets (e.g. `url.username.password`).

    Parameters
    ----------
    line : str
        The raw input line to parse.
    _attempt_fallback : bool, optional
        Internal flag to prevent infinite recursion during fallback parsing.  End
        users should not specify this argument.

    Returns
    -------
    Optional[Tuple[str, str, str]]
        A tuple of `(url, user, pass)` if parsing succeeds, otherwise ``None``.
    """
    line = line.strip()
    if not line:
        return None

    # 1. JSON/JSONL parsing: detect dictionaries with url/user/pass fields
    try:
        data = json.loads(line)
        if isinstance(data, dict):
            url = data.get("url", "").strip()
            user = data.get("user", data.get("username", "")).strip()
            pwd = data.get("pass", data.get("password", "")).strip()
            # Prepend scheme if missing
            if url and not url.startswith(('http://', 'https://')):
                if url.startswith('//'):
                    url = 'https:' + url
                else:
                    url = 'https://' + url
            if is_valid_url_part(url) and is_valid_user_part(user) and is_valid_pass_part(pwd):
                return url, user, pwd
    except (json.JSONDecodeError, AttributeError, TypeError):
        # Not a JSON object; proceed with delimiter-based parsing
        pass

    # 2. Delimiter-based parsing
    # Replace a wide range of separators with a pipe ('|').  Excluded characters
    # are dots and dashes because they can appear legitimately in domains and
    # paths.  Additional Unicode arrows and bullets are also replaced.
    # Note: equal sign, comma, at, hash, semicolon and whitespace are unified.
    # Regex matching one or more characters that should act as delimiters.  This
    # includes semicolons, hashes, equals, commas, whitespace,
    # pipes and a selection of Unicode arrows or bullets encountered in
    # unstructured credential dumps.  Dashes and dots are intentionally
    # excluded because they frequently appear in URLs and usernames; they are
    # handled via specialised fallback logic below.
    # Construct a regex pattern for characters we treat as field separators.  We intentionally
    # exclude the dot (.) and dash (-) characters here because they frequently appear
    # legitimately in domain names or usernames.  Unicode arrows/bullets from data dumps
    # are normalised to a single pipe as well.  We also deliberately omit the '@' here
    # and handle it separately below so that email addresses are preserved unless the
    # at-symbol is clearly acting as a delimiter.
    delim_regex = (
        r'[;#=,\s\|\u2022\u2192\u21dd\u21e8\u21b5\u22a2\u27f3]+'
    )
    # Replace recognised delimiters with a pipe for easier splitting
    line_norm = re.sub(delim_regex, '|', line)
    # Split into parts on pipes
    parts_raw = [p.strip().strip('"\'\'') for p in line_norm.split('|') if p.strip()]
    if not parts_raw:
        return None
    # Handle '@' separators carefully: split only when the '@' does not denote an email address.
    parts_intermediate: List[str] = []
    for part in parts_raw:
        if '@' in part:
            segments = part.split('@')
            # If more than one '@', treat all as delimiters
            if len(segments) > 2:
                parts_intermediate.extend([seg for seg in segments if seg])
                continue
            # Exactly one '@'
            local, domain = segments[0], segments[1]
            # If the segment after '@' looks like a domain (contains dot and letters), keep as email
            if '.' in domain and any(c.isalpha() for c in domain):
                parts_intermediate.append(part)
            else:
                # Treat '@' as delimiter separating user and password
                if local:
                    parts_intermediate.append(local)
                if domain:
                    parts_intermediate.append(domain)
        else:
            parts_intermediate.append(part)

    # Further split parts containing ':' into separate user/pass segments, but
    # avoid splitting URLs at the scheme colon.  Also filter out empty segments.
    parts: List[str] = []
    for part in parts_intermediate:
        if ':' in part:
            # Preserve the scheme (e.g. http://) but split on all additional colons
            scheme_end = 0
            try:
                if part.lower().startswith(('http://', 'https://')):
                    scheme_end = part.find('://') + 3
            except Exception:
                scheme_end = 0
            remainder = part[scheme_end:]
            if ':' in remainder:
                # Split remainder by all colons; the first segment belongs with the URL
                segments = remainder.split(':')
                # Append the URL portion (scheme + first segment)
                url_prefix = part[:scheme_end] + segments[0]
                if url_prefix:
                    parts.append(url_prefix)
                # Append all subsequent segments as separate parts
                for seg in segments[1:]:
                    if seg:
                        parts.append(seg)
                continue
            # No extra colons beyond the scheme; preserve entire part
            parts.append(part)
        else:
            parts.append(part)
    # Remove any remaining empty strings
    parts = [p for p in parts if p]
    # If we have fewer than two parts, we cannot extract a triple via the primary
    # parsing logic.  However, we may still recover a result via the fallback
    # mechanism for dot- or dash-separated credentials.  Only return None if
    # fallback is disabled or does not yield a valid result.
    if len(parts) < 2:
        if _attempt_fallback:
            # Only attempt fallback if there is a dot or dash in the original line and common login indicators
            login_indicators = r'/wp-|/login|/auth|/administrator|/admin|/signin|/sign|/drupal|/user/login'
            if re.search(login_indicators, line, re.IGNORECASE):
                for delim in ['.', '-']:
                    if delim in line:
                        parts_split = line.rsplit(delim, 2)
                        if len(parts_split) == 3:
                            fallback_line = f"{parts_split[0]}|{parts_split[1]}|{parts_split[2]}"
                            result = parse_line_robust(fallback_line, _attempt_fallback=False)
                            if result:
                                return result
        # If fallback did not return, give up
        return None

    # Cap the number of parts considered to limit combinatorial explosion on noisy lines
    if len(parts) > 9:
        parts = parts[:9]

    best_match: Optional[Tuple[str, str, str]] = None
    max_score = -1
    # Try all combinations of three distinct parts and all permutations thereof to find
    # the most plausible (url, user, pass) triple.  A scoring heuristic favours
    # sequences that look like a valid URL, a likely username and a plausible
    # password.  We limit combinations to 9 parts (above) to avoid combinatorial
    # explosions on noisy lines.
    from itertools import combinations, permutations
    if len(parts) >= 3:
        for combo in combinations(parts, 3):
            for p in permutations(combo):
                url_candidate, user_candidate, pass_candidate = p
                score = 0
                if is_valid_url_part(url_candidate):
                    score += 3
                if is_valid_user_part(user_candidate):
                    score += 2
                if is_valid_pass_part(pass_candidate):
                    score += 1
                # Additional tie-breaking heuristics: prefer the user to be
                # non-numeric/non-numeric-ending and the password to contain digits
                # or mixed case.  These adjustments are small so they only affect
                # ordering when multiple permutations have identical primary scores.
                if score >= 5:
                    # Penalise a username that ends with digits (more likely a password)
                    if user_candidate and user_candidate[-1].isdigit():
                        score -= 0.2
                    # Reward a username that contains '@', underscore or dot
                    if any(ch in user_candidate for ch in ['@', '_', '.']):
                        score += 0.1
                    # Reward a password that contains digits and letters
                    if any(c.isdigit() for c in pass_candidate) and any(c.isalpha() for c in pass_candidate):
                        score += 0.1
                    # Penalise a password that contains an '@' (more likely a username)
                    if '@' in pass_candidate:
                        score -= 0.2
                    # Penalise if the user field contains common password keywords
                    if re.search(r'pass|pwd', user_candidate, re.IGNORECASE):
                        score -= 0.3
                    # Reward if the pass field contains common password keywords (hinting it's a password)
                    if re.search(r'pass|pwd', pass_candidate, re.IGNORECASE):
                        score += 0.3
                if score > max_score:
                    max_score = score
                    best_match = (url_candidate, user_candidate, pass_candidate)
    # If a confident match is found, normalise the URL scheme and return
    if best_match and max_score >= 5:
        url, user, pwd = best_match
        # Normalise URL scheme
        if not url.startswith(('http://', 'https://')):
            if url.startswith('//'):
                url = 'https:' + url
            else:
                url = 'https://' + url
        # Normalise user/pass ordering heuristically: if the user field looks more
        # like a password and the password field looks more like a username, swap them.
        def looks_like_username(val: str) -> bool:
            """
            Heuristic to determine if a token is more likely a username than a password.

            A username often contains an at-sign (e‑mail), underscore or dot and
            typically comprises mostly alphabetic characters.  Tokens that are
            purely numeric or contain a high ratio of digits are far less
            likely to be usernames.  Additionally, well‑known administrator
            strings are treated as usernames.
            """
            if not val:
                return False
            v = val.lower()
            # Known admin-related identifiers
            if v in ('admin', 'administrator', 'administratorweb', 'administrator web', 'administratorweb', 'administrator'):  # duplicate but safe
                return True
            # Email addresses contain '@'
            if '@' in v:
                return True
            # Underscores or dots are common in usernames
            if '_' in v or '.' in v:
                return True
            # Avoid strings that look like passwords based on common keywords
            if 'pass' in v or 'pwd' in v:
                return False
            # Calculate digit ratio; if the token contains more digits than letters, it likely isn't a username
            letters = sum(1 for c in v if c.isalpha())
            digits = sum(1 for c in v if c.isdigit())
            # If there are no letters, it's not a username
            if letters == 0:
                return False
            # If digits dominate over letters, treat as non-username
            if digits >= letters:
                return False
            # Otherwise treat as username
            return True
        def looks_like_password(val: str) -> bool:
            """
            Heuristic to determine if a token is more likely a password than a username.

            Passwords often contain a mixture of letters and digits or end with digits.
            Strings without any alphabetic characters are unlikely to be meaningful
            credentials and are excluded.  Note that the presence of special
            characters (e.g. punctuation) is not explicitly required, as many
            simple passwords contain only alphanumerics.
            """
            if not val:
                return False
            has_alpha = any(c.isalpha() for c in val)
            has_digit = any(c.isdigit() for c in val)
            # Must contain some letters to be a plausible password
            if not has_alpha:
                return False
            # If it contains common password keywords, treat as password
            if re.search(r'pass|pwd', val, re.IGNORECASE):
                return True
            # If it contains both letters and digits, it's likely a password
            if has_alpha and has_digit:
                return True
            # If it ends with digits, likely a password
            if val[-1].isdigit():
                return True
            return False
        if looks_like_password(user) and looks_like_username(pwd):
            user, pwd = pwd, user
        return url, user, pwd

    # 3. Fallback handling for dot- or dash-separated credentials
    if _attempt_fallback:
        # Only attempt fallback if there is a dot or dash in the line and common login indicators
        login_indicators = r'/wp-|/login|/auth|/administrator|/admin|/signin|/sign|/drupal|/user/login'
        if re.search(login_indicators, line, re.IGNORECASE):
            for delim in ['.', '-']:
                if delim in line:
                    parts_split = line.rsplit(delim, 2)
                    if len(parts_split) == 3:
                        fallback_line = f"{parts_split[0]}|{parts_split[1]}|{parts_split[2]}"
                        result = parse_line_robust(fallback_line, _attempt_fallback=False)
                        if result:
                            return result
    return None


def detect_encoding(file_path: str) -> str:
    """Detects file encoding by checking BOMs and trying UTF-8, falls back to latin-1."""
    try:
        with open(file_path, 'rb') as f:
            # Read a chunk of the file to check for BOMs or typical UTF-8 patterns
            # Larger chunk might be more reliable but slower. 4096 is common.
            chunk_size = 4096
            # Ensure we don't try to read past EOF for small files
            raw = f.read(min(chunk_size, os.path.getsize(file_path)))

            # Check for Byte Order Marks (BOMs)
            if raw.startswith(b'\xef\xbb\xbf'): return 'utf-8-sig' # UTF-8 with BOM
            if raw.startswith(b'\xff\xfe'): return 'utf-16-le'    # UTF-16 Little Endian
            if raw.startswith(b'\xfe\xff'): return 'utf-16-be'    # UTF-16 Big Endian
            if raw.startswith(b'\x00\x00\xfe\xff'): return 'utf-32-be' # UTF-32 Big Endian
            if raw.startswith(b'\xff\xfe\x00\x00'): return 'utf-32-le' # UTF-32 Little Endian

            # Attempt to decode as UTF-8 (common default)
            try:
                raw.decode('utf-8')
                return 'utf-8' # If no BOM and decodes as UTF-8, assume UTF-8
            except UnicodeDecodeError:
                # If UTF-8 fails, fallback to latin-1 (ISO-8859-1)
                # latin-1 can decode any byte sequence, so it's a safe fallback
                # but might not be the "correct" original encoding.
                return 'latin-1' # Fallback if not UTF-8 and no BOM
    except Exception as e:
        logging.debug(f"Error detecting encoding for '{file_path}': {e}. Defaulting to utf-8 with error replacement.", exc_info=True)
        return 'utf-8' # Ultimate fallback with error replacement in case of issues


def load_processed_files(log_path: str) -> Set[str]:
    processed: Set[str] = set()
    if not os.path.exists(log_path):
        logging.debug(f"Processed files log not found: {log_path}. Starting with empty set of processed files.")
        return processed

    log_lock_path = log_path + '.lock' # Define lock file path for the log
    try:
        # Attempt to acquire a lock before reading the log file
        # This is to prevent conflicts if another instance tries to write to it (though less likely for reads)
        try:
             logging.debug(f"Attempting to acquire lock for reading log: {log_lock_path}")
             with FileLock(log_lock_path, timeout=5) as lock: # Pass timeout here
                logging.debug(f"Lock acquired for reading log file: {log_path}")
                with open(log_path, 'r', encoding='utf-8', errors='ignore') as f:
                    for i, line in enumerate(f):
                        if i > 0 and i % 10000 == 0: # Log progress for very large logs
                            logging.debug(f"  Log load progress: {i:,} lines processed, {len(processed):,} files added from {os.path.basename(log_path)}.")
                        file_path = line.strip()
                        if file_path: # Ensure non-empty lines
                            processed.add(os.path.abspath(file_path)) # Store absolute paths for consistency
                logging.debug(f"Finished reading log file: {log_path}. Found {len(processed)} entries.")
             logging.debug(f"Lock released for log file: {log_lock_path}")

        except RuntimeError as re: # Specific error from FileLock timeout
            logging.warning(f"Could not acquire lock for processed files log ({os.path.basename(log_path)}) within timeout. Skipping loading existing log. Files may be re-processed. Error: {re}", exc_info=True)
            processed = set() # Return empty set as if log didn't exist or was unreadable
        except Exception as e:
            logging.error(f"Error reading processed files log '{log_path}': {e}", exc_info=True)
            # Decide if you want to return an empty set or re-raise, depending on desired fault tolerance
            # For robustness, returning an empty set might be preferred over crashing.
            processed = set()

    except Exception as outer_e: # Catch errors from FileLock initialization itself
        logging.error(f"Failed to initialize lock for processed files log loading process: {outer_e}", exc_info=True)
        processed = set()
    return processed


def log_processed_file(log_path: str, file_path: str):
    log_lock_path = log_path + '.lock'
    try:
        # Acquire lock before appending to the log file
        try:
            logging.debug(f"Attempting to acquire lock for writing log: {log_lock_path}")
            with FileLock(log_lock_path, timeout=5) as lock: # Pass timeout here
                logging.debug(f"Lock acquired for writing log file: {log_path}")
                with open(log_path, 'a', encoding='utf-8', newline='\n') as f:
                    f.write(os.path.abspath(file_path) + '\n') # Write absolute path
                logging.debug(f"Logged processed file: {os.path.abspath(file_path)} to {os.path.basename(log_path)}")
            logging.debug(f"Lock released for log file: {log_lock_path}")
        except RuntimeError as re: # FileLock timeout
            logging.warning(f"Could not acquire lock to log processed file ({os.path.basename(log_path)}) within timeout. File '{os.path.abspath(file_path)}' may be re-processed later. Error: {re}", exc_info=True)
        except Exception as e: # Other errors during file write
             logging.error(f"Error writing to processed files log '{log_path}': {e}", exc_info=True)
    except Exception as outer_e: # Errors from FileLock initialization
        logging.error(f"Failed to initialize lock for processed files log writing process: {outer_e}", exc_info=True)


def watchdog_thread(progress_state: Dict[str, Any], timeout_seconds: int):
    last_progress_bytes = 0
    last_check_time = time.time()
    logging.debug("Watchdog thread started, waiting for initial grace period.")
    time.sleep(5) # Initial grace period

    while not progress_state.get('stop_requested', False): # Check global stop flag
        current_progress_bytes = progress_state.get('bytes', 0)
        current_time = time.time()

        if current_progress_bytes > 0 and current_progress_bytes == last_progress_bytes: # Progress stalled
            if current_time - last_check_time > timeout_seconds:
                file_name = progress_state.get('current_file', 'unknown file')
                logging.error(f"WATCHDOG: Processing stalled on file '{file_name}' for >{timeout_seconds}s ({last_progress_bytes:,} bytes processed). Aborting current file.")
                progress_state['watchdog_triggered'] = True
                progress_state['stop_requested'] = True # Signal main processing to stop for this file
                logging.debug("Watchdog triggered stop_requested flag.")
                break # Exit watchdog thread
        elif current_progress_bytes > last_progress_bytes: # Progress made
            last_progress_bytes = current_progress_bytes
            last_check_time = current_time # Reset timer
            logging.debug(f"Watchdog updated progress baseline for {progress_state.get('current_file', 'unknown file')}: {last_progress_bytes:,} bytes.")
        time.sleep(1) # Check interval
    logging.debug("Watchdog thread exiting.")


def input_listener_thread(progress_state: Dict[str, Any]):
    if not _has_working_kb_input:
        logging.debug("Input listener disabled: _has_working_kb_input is False.")
        return

    is_posix_tty_for_input = sys.platform != 'win32' and sys.stdin.isatty()
    raw_input_enabled_here = False # Local flag for this function's raw mode management

    if is_posix_tty_for_input:
         raw_input_enabled_here = _enable_raw_input() # Try to enable raw input
         if not raw_input_enabled_here:
             # If enabling raw input failed, log it but proceed cautiously.
             # _getch_posix might not work as expected without raw mode.
             logging.debug("Input listener failed to enable raw mode. Input might be buffered or echoed.")
             # We don't set is_posix_tty_for_input to False here, as _getch_posix might still attempt to read.

    logging.debug("Input listener thread started, listening for keypresses.")

    try:
        while not progress_state.get('stop_listener', False): # Controlled by main thread for shutdown
            if _kbhit(): # Check if a key is pressed
                try:
                    key = _getch() # Get the key
                    logging.debug(f"Input listener caught key: {key!r}")
                    # Common keys for interruption/skip: Enter, Space, Ctrl+C (represented as b'\x03')
                    if key in (b'\r', b'\n', b' ', b'\x03'): # b'\x03' is typically Ctrl+C
                        if key == b'\x03': # Specifically log Ctrl+C if that's what we want to treat as skip
                             logging.debug("Input listener detected Ctrl+C keypress as skip.")
                        logging.warning(f"User initiated skip for file: {progress_state.get('current_file', 'unknown file')}")
                        progress_state['manual_skip_requested'] = True
                        progress_state['stop_requested'] = True # Signal file processing to stop
                        time.sleep(0.05) # Brief pause
                        # Attempt to clear any buffered input after skip
                        logging.debug("Clearing input buffer after skip keypress.")
                        while _kbhit():
                            try:
                                _getch() # Read and discard
                            except: # Catch any error during buffer clear
                                break
                        time.sleep(0.1) # Small delay after clearing
                except Exception as e_key:
                    logging.debug(f"Input listener key processing error: {e_key}", exc_info=True)
            time.sleep(0.05) # Polling interval for _kbhit()
    finally:
        # Restore terminal settings if they were changed by this thread's call to _enable_raw_input
        if raw_input_enabled_here: # Only restore if this instance enabled it
            _restore_normal_input()
            logging.debug("Input listener thread restored terminal settings.")
        else:
            logging.debug("Input listener thread exiting; no terminal settings to restore by this instance or raw mode was not enabled.")
    logging.debug("Input listener thread exiting gracefully.")


def process_file(
    file_path: str,
    keywords: List[str],
    output_file, # File handle for writing output
    wordpress_output_file, # File handle for WordPress output
    unique_lines: Set[Tuple[str, str, str]], # MODIFIED: Now a set of (url, user, pass) tuples
    pbar_file: Optional[tqdm], # Progress bar for current file
    progress_state: Dict[str, Any] # Shared state for watchdog and input listener
) -> int:
    added_count = 0
    lines_read_total = 0
    watchdog_timeout = 180 # 3 minutes, adjust as needed
    processing_error = False # Flag to indicate if an error occurred that warrants skipping the file
    buffer: List[str] = [] # Initialize buffer for batch writing (still stores JSON strings)

    # Reset progress_state for the new file
    progress_state.update({
        'bytes': 0,
        'lines': 0,
        'hits': 0,
        'file_size': -1, # Will be updated
        'watchdog_triggered': False,
        'manual_skip_requested': False,
        'stop_requested': False, # Reset for current file processing
        'current_file': os.path.basename(file_path),
    })
    logging.debug(f"Starting process_file for '{file_path}'. Initial state updated: {progress_state}")

    file_basename = os.path.basename(file_path)
    # Start watchdog for this file
    watchdog = threading.Thread(target=watchdog_thread, args=(progress_state, watchdog_timeout), daemon=True)
    watchdog.start()
    logging.debug(f"Watchdog thread started for file '{file_basename}' (timeout: {watchdog_timeout}s).")

    try:
        # Initial file checks (size, existence)
        try:
            f_size = os.path.getsize(file_path)
            progress_state['file_size'] = f_size
            logging.debug(f"File size for '{file_basename}': {f_size:,} bytes.")
            if f_size == 0:
                if pbar_file: pbar_file.set_postfix_str("Empty", refresh=True)
                logging.debug(f"Skipping empty file: {file_path}")
                progress_state['stop_requested'] = True # Signal watchdog to stop for this file
                return 0 # No lines added from an empty file
        except FileNotFoundError:
            logging.error(f"File not found during initial size check for '{file_path}'! Skipping this file.", exc_info=True)
            processing_error = True
            progress_state['stop_requested'] = True
        except Exception as e: # Catch other OS errors like permission denied
            logging.error(f"Error getting size or during initial checks for '{file_path}': {e}! Skipping this file.", exc_info=True)
            processing_error = True
            progress_state['stop_requested'] = True

        if processing_error: # If initial checks failed, don't proceed further
             if pbar_file: pbar_file.set_postfix_str("Error (Init)", refresh=True)
             logging.debug(f"process_file for '{file_basename}' detected initial error, skipping rest of try block.")
             # No need to raise, just let it fall through to finally block after this 'try'
             return -1 # Indicate error

        encoding = detect_encoding(file_path)
        logging.debug(f"Detected encoding for '{file_basename}': {encoding}")

        if pbar_file:
            pbar_file.reset(total=f_size) # Reset progress bar for current file size
            pbar_file.set_description_str(f"{file_basename[:20]:<20} ({encoding})", refresh=False) # Update description
            pbar_file.update(0) # Start at 0

        # Main file processing loop (line by line)
        # This approach is memory-efficient for large files.
        with open(file_path, 'r', encoding=encoding, errors='replace') as f_std:
            buffer_max_size = 20000 # Number of lines to buffer before writing
            logging.debug(f"Starting line processing loop for '{file_basename}'. Buffer max size: {buffer_max_size}.")

            for line_text in f_std:
                if progress_state.get('stop_requested', False): # Check for skip/watchdog/error signals
                    logging.debug(f"'stop_requested' flag is True for '{file_basename}'. Breaking line processing loop.")
                    break # Exit loop if stop is requested

                lines_read_total += 1
                progress_state['lines'] = lines_read_total
                try:
                    # Estimate bytes processed for progress bar. Encoding matters.
                    progress_state['bytes'] += len(line_text.encode(encoding, errors='replace'))
                except Exception as e: # Fallback if encoding for len fails (unlikely with 'replace')
                    logging.debug(f"Error estimating bytes for progress bar on line {lines_read_total}: {e}. Using character count.", exc_info=True)
                    progress_state['bytes'] += len(line_text) # Fallback to char count

                # Update progress bar periodically, not on every line for performance
                if pbar_file and lines_read_total % 1000 == 0:
                    pbar_file.update(progress_state['bytes'] - pbar_file.n) # Update by delta
                    pbar_file.set_postfix_str(f"Lines:{lines_read_total:,} Added:{added_count}", refresh=False)

                line_stripped = line_text.strip()
                if not line_stripped: # Skip empty lines
                    continue

                # Keyword filtering (if keywords are provided)
                # This is case-insensitive as keywords are lowercased on input, and line_lower is used.
                if keywords:
                     line_lower = line_stripped.lower()
                     if not any(k in line_lower for k in keywords): # k is already lowercase
                        continue
                progress_state['hits'] += 1 # Count lines that pass keyword filter (or all if no keywords)

                # Parsing logic (robustly)
                credential_tuple = parse_line_robust(line_stripped)

                if credential_tuple:
                    # Unpack the parsed tuple
                    orig_url_part, user_part, pass_part = credential_tuple
                    # Normalise the URL to the appropriate CMS login endpoint
                    login_url_part = get_login_url(orig_url_part)
                    # Update WordPress domain list if applicable
                    wp_base = extract_wordpress_base(login_url_part)
                    if wp_base:
                        wordpress_domains_set.add(wp_base)
                    # Build a new credential tuple using the normalised URL
                    new_credential_tuple = (login_url_part, user_part, pass_part)
                    # Deduplicate based on the new credential tuple
                    if new_credential_tuple not in unique_lines:
                        unique_lines.add(new_credential_tuple)
                        # Prepare the output line using the new separators
                        line_to_write = f"{login_url_part}#{user_part}@{pass_part}"
                        buffer.append(line_to_write)
                        added_count += 1
                        # CMS detection and logging. Use detect_cms() to determine
                        # which CMS/frameworks the URL likely belongs to. For each
                        # detected CMS, add to its unique credential set and write
                        # to the corresponding output file.
                        try:
                            cms_list = detect_cms(login_url_part)
                            for cms_key in cms_list:
                                # Skip if CMS is not tracked (safety check)
                                if cms_key not in cms_unique_credentials:
                                    continue
                                if new_credential_tuple not in cms_unique_credentials[cms_key]:
                                    cms_unique_credentials[cms_key].add(new_credential_tuple)
                                    f_handle = cms_output_files.get(cms_key)
                                    if f_handle is not None and not f_handle.closed:
                                        try:
                                            f_handle.write(f"{login_url_part}#{user_part}@{pass_part}\n")
                                            f_handle.flush()
                                        except Exception as cms_write_e:
                                            logging.error(
                                                f"Failed to write to {cms_key} output file: {cms_write_e}",
                                                exc_info=True,
                                            )
                        except Exception as cms_detect_e:
                            # Catch any unexpected errors in CMS detection to avoid
                            # disrupting the main extraction flow.
                            logging.error(
                                f"Unexpected error during CMS detection for URL '{login_url_part}': {cms_detect_e}",
                                exc_info=True,
                            )

                    # Write buffer to file if it's full
                    if len(buffer) >= buffer_max_size:
                        try:
                            output_file.write('\n'.join(buffer) + '\n')
                            buffer.clear()
                            output_file.flush()
                        except Exception as write_e:
                            logging.error(f"Error writing buffer to output file: {write_e}", exc_info=True)

    except FileNotFoundError: # Should be caught by initial check, but as a safeguard here too
        logging.error(f"File not found during processing loop for '{file_path}'! Skipping this file.", exc_info=True)
        processing_error = True
        progress_state['stop_requested'] = True # Ensure watchdog knows
    except IOError as e: # Broader I/O errors (e.g., disk full, read errors)
        logging.error(f"I/O Error while processing '{file_path}': {e}! Skipping this file.", exc_info=True)
        processing_error = True
        progress_state['stop_requested'] = True
    except Exception as e: # Catch-all for unexpected errors during file processing
        logging.error(f"Unexpected error processing '{file_path}': {e}! Skipping this file.", exc_info=True)
        processing_error = True
        progress_state['stop_requested'] = True
    finally:
        logging.debug(f"Entered finally block for process_file for '{file_basename}'.")
        # Write any remaining lines in the buffer
        if buffer: # Check if buffer has items
            logging.debug(f"Writing remaining buffer ({len(buffer)} lines) to output file in finally block for '{file_basename}'.")
            try:
                if output_file and not output_file.closed: # Ensure output_file is valid and open
                    output_file.write('\n'.join(buffer) + '\n')
                    output_file.flush()
                    logging.debug("Remaining buffer successfully written and flushed in finally.")
                else:
                    logging.warning(f"Output file was closed or invalid when trying to write remaining buffer for {file_basename}.")
            except Exception as final_write_e:
                 logging.error(f"Error writing final buffer in finally block for '{file_basename}': {final_write_e}.", exc_info=True)

        # Signal watchdog to stop and wait for it to terminate
        progress_state['stop_requested'] = True # Ensure it's set for watchdog to exit
        logging.debug(f"Explicitly set 'stop_requested' = True for '{file_basename}''s watchdog thread in finally block.")
        try:
            watchdog.join(timeout=2) # Wait for watchdog with a timeout
            if watchdog.is_alive():
                 logging.warning(f"Watchdog thread for '{file_basename}' did not terminate cleanly within timeout.")
            else:
                 logging.debug(f"Watchdog thread for '{file_basename}' joined successfully.")
        except Exception as join_e: # Should not happen if thread is daemon, but good practice
            logging.error(f"Error joining watchdog thread for '{file_basename}': {join_e}", exc_info=True)

        # Determine final status for progress bar
        manual_skipped = progress_state.get('manual_skip_requested', False)
        watchdog_triggered = progress_state.get('watchdog_triggered', False)
        # Aborted if any of these conditions met. Note: processing_error is set by except blocks.
        aborted = manual_skipped or watchdog_triggered or processing_error

        if pbar_file:
            status = "Done"
            if manual_skipped: status = "Skipped (User)"
            elif watchdog_triggered: status = "Stalled (WD)"
            elif processing_error: status = "Error (Proc)"
            
            # Ensure progress bar completes to 100% if not aborted and processing finished early
            # (e.g. stop_requested was true from main thread, but file itself was fine)
            if not aborted and pbar_file.n < pbar_file.total:
                 # Only update if there's a meaningful delta; avoid if total is 0 (empty file)
                 if pbar_file.total > 0:
                    remaining_progress = pbar_file.total - pbar_file.n
                    if remaining_progress > 0:
                        try:
                            pbar_file.update(remaining_progress)
                        except Exception as pbar_update_e:
                            logging.debug(f"Error updating pbar {file_basename} to full in finally: {pbar_update_e}")
            
            pbar_file.set_postfix_str(f"Lines:{lines_read_total:,} Added:{added_count} - {status}", refresh=True)
            pbar_file.refresh() # Ensure final status is displayed

        logging.debug(f"Finished process_file for '{file_basename}'. Result: Lines read={lines_read_total:,}, Unique added (this file)={added_count}, Aborted={aborted}.")
        return added_count if not aborted else -1 # Return count or -1 if aborted/error

# Signal handler for graceful shutdown
exit_flag = False # Global flag to signal exit
def handle_sigint(sig, frame):
    global exit_flag
    # Use print for immediate feedback as logging might be delayed or not visible during shutdown
    # Check if stdout is a TTY to avoid writing control codes if output is piped
    if sys.stdout.isatty():
        sys.stdout.write("\n⚠️ Interrupt signal received. Initiating graceful shutdown and cleanup...\n")
        sys.stdout.flush()
    else: # Non-TTY, simpler message
        print("Interrupt signal received. Initiating graceful shutdown.")
    
    logging.warning("Interrupt signal received. Initiating shutdown sequence.")
    exit_flag = True


def sort_and_deduplicate(output_path: str) -> int:
    """
    Reads lines from output_path, deduplicates, sorts, and overwrites the file.
    This operation is IN-MEMORY and may fail for extremely large output files.
    """
    if not os.path.exists(output_path) or os.path.getsize(output_path) == 0:
        if os.path.exists(output_path): # File exists but is empty
             logging.debug(f"Output file '{os.path.basename(output_path)}' exists but is empty ({os.path.getsize(output_path):,} bytes). Skipping final sort/dedupe.")
        else: # File does not exist
             logging.debug(f"Output file '{os.path.basename(output_path)}' not found. Skipping final sort/dedupe.")
        return 0

    logging.info(f"Finalizing output file '{os.path.basename(output_path)}': Reading, deduplicating, and sorting {os.path.getsize(output_path):,} bytes of text lines.")
    unique_lines_set: Set[str] = set()
    try:
        # Read all lines from the file into a set for deduplication
        with open(output_path, 'r', encoding='utf-8', errors='ignore') as f_in:
            for i, line in enumerate(f_in):
                 if i > 0 and i % 100000 == 0: # Progress for large files
                      logging.info(f"  Sort/Dedupe read progress: {i:,} lines processed from '{os.path.basename(output_path)}', {len(unique_lines_set):,} unique collected so far.")
                 stripped = line.strip()
                 if stripped: # Add non-empty lines
                    unique_lines_set.add(stripped)
        logging.info(f"Finished reading '{os.path.basename(output_path)}'. Found {len(unique_lines_set):,} unique lines.")

        # Sort the unique lines
        # Note: This list conversion and sort can also be memory-intensive for huge sets.
        sorted_lines = sorted(list(unique_lines_set))
        final_unique_count = len(sorted_lines)
        logging.debug(f"Sorting complete. Prepared {final_unique_count:,} unique lines to write back to '{os.path.basename(output_path)}'.")

        if final_unique_count > 0:
            logging.debug(f"Writing {final_unique_count:,} unique lines back to '{output_path}'.")
            # Overwrite the original file with sorted, unique lines
            with open(output_path, 'w', encoding='utf-8', newline='\n') as f_out:
                f_out.write('\n'.join(sorted_lines) + '\n')
            logging.info(f"Output file '{os.path.basename(output_path)}' finalized successfully with {final_unique_count:,} unique lines.")
        else: # No unique lines found, or all were empty
            logging.warning(f"Finalization resulted in 0 unique lines for '{os.path.basename(output_path)}'. Overwriting file as empty.")
            try:
                with open(output_path, 'w', encoding='utf-8', newline='\n') as f_out:
                    pass # Create an empty file
            except Exception as e_empty_write:
                 logging.warning(f"Failed to overwrite output file '{output_path}' as empty after finding 0 unique lines: {e_empty_write}", exc_info=True)
        return final_unique_count
    except Exception as e:
        logging.error(f"Error finalizing output file '{output_path}': {e}", exc_info=True)
        # Return count of lines collected before error, if any
        return len(unique_lines_set) if 'unique_lines_set' in locals() and unique_lines_set else 0


def merge_output_files(output_dir: str, output_pattern_template: str, merge_file_name: str) -> int:
    """
    Merges all instance-specific output files into a single, sorted, deduplicated file.
    This operation is IN-MEMORY and may fail for extremely large combined outputs.
    """
    logging.info(f"Starting merge operation in '{output_dir}'. Target file: '{merge_file_name}'.")
    try:
        # Determine the prefix of files to merge (e.g., "extracted_lines_")
        pattern_prefix = output_pattern_template.split('{', 1)[0]
        merged_file_path = os.path.join(output_dir, merge_file_name)

        try:
            all_items_in_output_dir = os.listdir(output_dir)
            logging.debug(f"Scanned directory '{output_dir}'. Found {len(all_items_in_output_dir)} items.")
        except FileNotFoundError:
            logging.warning(f"Output directory '{output_dir}' not found during merge scan. No files available to merge.")
            return 0 # No files to merge if directory doesn't exist

        output_files_to_read: List[str] = []
        for item_name in all_items_in_output_dir:
            full_item_path = os.path.join(output_dir, item_name)
            # Identify files matching the pattern, are .jsonl, and are not the merge file itself
            if os.path.isfile(full_item_path) \
               and item_name.startswith(pattern_prefix) \
               and item_name.lower().endswith('.txt') \
               and item_name.lower() != merge_file_name.lower(): # Exclude the target merge file from sources
                 output_files_to_read.append(full_item_path)
        
        logging.info(f"Identified {len(output_files_to_read)} individual output files matching pattern '{pattern_prefix}*.txt' for merging.")
        if output_files_to_read: # Log only if there are files
            logging.debug(f"Individual files to merge: {output_files_to_read}")

        all_lines_set: Set[str] = set()

        # Optionally, load existing lines from the merge file itself to include them
        if os.path.exists(merged_file_path) and os.path.getsize(merged_file_path) > 0:
             try:
                logging.info(f"Loading existing unique lines from merge file '{os.path.basename(merged_file_path)}' ({os.path.getsize(merged_file_path):,} bytes) for deduplication.")
                with open(merged_file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    for i, line in enumerate(f):
                         if i > 0 and i % 100000 == 0:
                            logging.info(f"  Merge load progress (existing): {i:,} lines processed, {len(all_lines_set):,} unique collected.")
                         stripped = line.strip()
                         if stripped:
                            all_lines_set.add(stripped)
                logging.info(f"Finished loading existing merge file '{os.path.basename(merged_file_path)}'. Collected {len(all_lines_set):,} unique lines initially.")
             except Exception as e:
                logging.error(f"Error loading existing merge file '{merged_file_path}': {e}. Starting merge process with only individual files found.", exc_info=True)
                all_lines_set.clear() # Reset if loading failed, to avoid partial data

        # Read lines from all identified individual output files
        for file_path in output_files_to_read:
            if not os.path.exists(file_path) or os.path.getsize(file_path) == 0:
                logging.debug(f"Skipping empty or non-existent individual file during merge read: {file_path}")
                continue
            try:
                logging.debug(f"Reading individual file for merge: {os.path.basename(file_path)} ({os.path.getsize(file_path):,} bytes)")
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    for i, line in enumerate(f):
                         if i > 0 and i % 100000 == 0: # Progress for large individual files
                            logging.debug(f"  Merge read progress ({os.path.basename(file_path)}): {i:,} lines processed, {len(all_lines_set):,} total unique collected.")
                         stripped = line.strip()
                         if stripped:
                            all_lines_set.add(stripped)
                logging.debug(f"Finished reading '{os.path.basename(file_path)}'. Current total unique: {len(all_lines_set):,}.")
            except Exception as e:
                logging.error(f"Error reading file '{file_path}' during merge process: {e}", exc_info=True)
                # Continue with other files if one fails

        if not all_lines_set: # No lines collected from any source
             logging.warning(f"No unique lines found across all merge sources after reading. Creating/overwriting '{os.path.basename(merged_file_path)}' as empty.")
             try:
                 # Create an empty merge file
                 with open(merged_file_path, 'w', encoding='utf-8', newline='\n') as f_out:
                     pass # Just create/truncate the file
                 logging.debug(f"Empty merge file '{merged_file_path}' created/overwritten.")
             except Exception as e_create_empty:
                 logging.warning(f"Failed to create empty merge file '{merged_file_path}': {e_create_empty}")
             return 0 # Return 0 as no lines were merged

        logging.info(f"Sorting {len(all_lines_set):,} unique lines for merge...")
        sorted_lines = sorted(list(all_lines_set)) # Memory-intensive step
        final_merged_count = len(sorted_lines)
        logging.info(f"Sorting complete. Preparing to write {final_merged_count:,} lines to '{os.path.basename(merged_file_path)}'.")

        try:
            # Write the sorted, unique lines to the final merge file
            with open(merged_file_path, 'w', encoding='utf-8', newline='\n') as f_out:
                f_out.write('\n'.join(sorted_lines) + '\n')
            logging.info(f"Merge operation successfully completed. Final file '{os.path.basename(merged_file_path)}' contains {final_merged_count:,} unique lines.")
            return final_merged_count
        except Exception as e: # Error during writing of merged file
             logging.error(f"Error writing merged output file '{merged_file_path}': {e}", exc_info=True)
             return 0 # Indicate failure or 0 lines written
    except Exception as e: # Catch-all for unexpected errors during merge setup or execution
        logging.critical(f"An unexpected critical error occurred during merge operation in '{output_dir}': {e}", exc_info=True)
        return 0 # Indicate critical failure

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=f"{APP_NAME} v{APP_VERSION} - Extracts and validates URL/Username/Password lines from text files, outputs as url#user@pass.",
        formatter_class=argparse.RawTextHelpFormatter # Allows newlines in help text
    )
    parser.add_argument("--input", "-i", type=str, default=DEFAULT_INPUT_DIR,
                        help=f"Input directory containing text files (.txt) to scan.\n"
                             f"Subdirectories will also be scanned.\n"
                             f"(default: {DEFAULT_INPUT_DIR})")
    parser.add_argument("--keywords", "-k", type=str, default="",
                        help="Comma-separated list of keywords to search for within each line.\n"
                             "Only lines containing at least one keyword (case-insensitive) are further processed.\n"
                             "Leave blank to skip keyword filtering and attempt to process all non-empty lines (after validation).\n"
                             "(default: blank - no keyword filter)")
    parser.add_argument("--output-dir", "-o", type=str, default=BASE_OUTPUT_DIR,
                        help=f"Base directory for saving output files.\n"
                             f"(default: {BASE_OUTPUT_DIR})")
    parser.add_argument("--log-dir", "-l", type=str, default=LOG_DIR,
                        help=f"Directory for saving log files.\n"
                             f"(default: {LOG_DIR})")
    parser.add_argument("--instance-id", type=str, default=None,
                        help="A custom identifier for this specific running instance.\n"
                             "Using different IDs allows multiple runs on the same output directory without conflicts.\n"
                             "Also allows resuming a specific instance's interrupted job by using the same ID.\n"
                             "(default: auto-generated identifier based on hostname, process ID, and short random hex string)")
    parser.add_argument("--merge", "-m", action="store_true",
                        help="Enable the merge feature. After processing, all 'filtered_*.txt' files in the output directory\n"
                             "will be merged into a single, deduplicated, and sorted file.")
    parser.add_argument("--merge-file", type=str, default="merged_output.txt",
                        help="The filename for the final merged output file when --merge is enabled.\n"
                             "(default: merged_output.txt)")
    parser.add_argument("--non-interactive", "-n", action="store_true",
                        help="Run in non-interactive mode. Skips interactive prompts for input directory and keywords (uses --input and --keywords).\n"
                             "Disables TQDM progress bars for command-line interfaces that don't support them.\n"
                             "Disables the interactive keyboard skip feature.")
    parser.add_argument("--debug", action="store_true",
                        help="Enable debug logging output. This displays significantly more detailed internal processing information, \n"
                             "useful for troubleshooting parsing or validation issues.")
    return parser.parse_args()

# Helper function for os.walk error handling
def _walk_error_logger(os_error: OSError):
    """Error handler for os.walk, logs the error and allows walk to continue."""
    logging.warning(
        f"Directory scan error: Cannot access path '{os_error.filename}' "
        f"due to: {os_error.strerror}. Skipping this item."
    )
    # To allow os.walk to continue, this function must not raise an exception.

def main():
    global exit_flag, INSTANCE_ID # Allow modification of global INSTANCE_ID if provided by arg
    exit_flag = False # Reset global exit flag

    args = parse_arguments()

    # Override INSTANCE_ID if provided via argument
    if args.instance_id:
        INSTANCE_ID = args.instance_id # Use user-provided instance ID
    
    # Determine log level based on --debug flag
    log_level = logging.DEBUG if args.debug else logging.INFO
    
    # BasicConfig is a fallback if setup_logging fails, or for very early messages.
    # setup_logging will replace these handlers.
    logging.basicConfig(level=logging.WARNING, format='%(asctime)s [%(levelname)-8s] - %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
    logging.debug("Basic logging configured temporarily (level: WARNING by default before setup_logging).")

    # Register SIGINT handler (Ctrl+C)
    signal.signal(signal.SIGINT, handle_sigint)
    logging.debug("SIGINT signal handler registered.")

    # Determine script directory (robustly)
    try:
        # __file__ is defined when running as a script
        script_dir = os.path.dirname(os.path.abspath(__file__))
    except NameError:
        # __file__ is not defined (e.g., interactive interpreter, frozen executable without this path)
        script_dir = os.getcwd() # Fallback to current working directory
    logging.debug(f"Script directory determined as: {script_dir}")

    # Prepare paths for output files.  Override the default locations to
    # follow the required folder structure: a top‑level 'keyword_output'
    # directory for keyword/credential outputs, a top‑level 'log' directory
    # for logs, and a top‑level 'cms-detect' directory (computed later) for
    # per‑CMS credential outputs.  Note that args.output_dir and args.log_dir
    # are ignored in favour of the fixed structure.
    output_dir = os.path.join(script_dir, 'keyword_output')
    log_dir = os.path.join(script_dir, 'log')
    output_file_name = OUTPUT_FILE_TEMPLATE.format(instance_id=INSTANCE_ID)
    processed_log_file = PROCESSED_FILES_LOG_TEMPLATE.format(instance_id=INSTANCE_ID)
    error_log_file = ERROR_LOG_TEMPLATE.format(instance_id=INSTANCE_ID)

    processed_log_path = os.path.join(log_dir, processed_log_file)
    output_path = os.path.join(output_dir, output_file_name)

    logging.debug(f"Instance output file path: {output_path}")
    logging.debug(f"Instance processed log path: {processed_log_path}")
    logging.debug(f"Instance error log file path: {os.path.join(output_dir, error_log_file)}")

    # -------------------------------------------------------------------
    # Prepare data structures for HTTP-based CMS detection.  If XML files
    # exported from Burp Suite are encountered during the input directory
    # scan, detections will be accumulated here.  Each CMS key maps to a
    # list of evidence records (strings) and a count of total detections.
    cms_http_records: Dict[str, List[str]] = {}
    cms_http_counts: Dict[str, int] = {}

    # Setup application-specific logging (replaces basicConfig handlers)
    setup_logging(log_dir, error_log_file, level=log_level)

    # Determine if running in an interactive TTY environment
    IS_INTERACTIVE_TTY = (sys.stdout.isatty() and sys.stdin.isatty()) and not args.non_interactive
    logging.debug(f"Is interactive TTY mode detected: {IS_INTERACTIVE_TTY}")

    # Handle non-interactive mode adjustments
    if not IS_INTERACTIVE_TTY:
        logging.info("Running in non-interactive mode (--non-interactive flag or not TTY). Disabling interactive features.")
        # Replace tqdm with a pass-through lambda if non-interactive
        global tqdm # Need to modify global tqdm
        _tqdm_orig = tqdm # Store original tqdm
        tqdm_lambda = lambda iterable, *args, **kwargs: iterable # tqdm(iterable) just returns iterable
        
        # Ensure tqdm.write compatibility if it's used directly
        # (TqdmLoggingHandler already has a fallback for non-TTY)
        if hasattr(_tqdm_orig, 'write') and callable(_tqdm_orig.write):
            # Create a stand-in write method that mimics tqdm.write's signature but uses print
            _tqdm_orig_write_method = _tqdm_orig.write 
            def _tqdm_write_fallback(s, file=None, end=None, nolock=False): # nolock might be used
                _stream = file if file is not None else sys.stdout
                _end = end if end is not None else '\n'
                _stream.write(s + _end)
                _stream.flush()
            
            # Assign new methods to the original tqdm object if it's a class,
            # or to a new object that mimics tqdm if tqdm was a function.
            # This is tricky due to tqdm's nature. For simplicity, if tqdm is the class:
            if isinstance(_tqdm_orig, type) and issubclass(_tqdm_orig, object): # Check if _tqdm_orig is tqdm class
                class TqdmNonInteractive(_tqdm_orig): # Inherit to keep other methods if any used
                    def __init__(self, iterable=None, *args, **kwargs):
                        if iterable is not None: # If used as iterator wrapper
                           super().__init__(iterable, *args, **kwargs) # Call parent for structure
                           self.iterable = iterable # Store iterable
                        # else: it might be used for tqdm.write directly
                    
                    def __iter__(self): # If used as iterator
                        return iter(self.iterable) if hasattr(self, 'iterable') else iter([])

                    def __enter__(self): return self # For context manager
                    def __exit__(self, *exc): return False

                    @staticmethod
                    def write(s, file=None, end=None, nolock=False): # Make it static like original
                        _tqdm_write_fallback(s, file=file, end=end)
                    
                    # Add other methods if they are directly called and need shimming
                    def update(self, n=1): pass
                    def close(self): pass
                    def set_description_str(self, s, refresh=True): pass
                    def set_postfix_str(self, s, refresh=True): pass
                    def reset(self, total=None): pass
                    def refresh(self, nolock=False, lock_args=None): pass


                tqdm = TqdmNonInteractive # Replace global tqdm with the non-interactive version
                logging.debug("Replaced global tqdm with a non-interactive TQDM shim class.")
            else: # If tqdm was already a simple function or unknown structure, simpler replacement
                tqdm = tqdm_lambda
                if hasattr(_tqdm_orig, 'write'): # If original had write, provide a fallback
                    tqdm.write = _tqdm_write_fallback # type: ignore
                logging.debug("Replaced global tqdm with a lambda; tqdm.write shimmed if present.")

        # Disable keyboard input functions
        global _kbhit, _getch, _kbhit_fallback, _getch_fallback, _has_working_kb_input
        _kbhit = _kbhit_fallback
        _getch = _getch_fallback
        _has_working_kb_input = False
        logging.debug("Keyboard input functions explicitly set to fallback (disabled) in non-interactive mode.")

    # --- Main Application Logic ---
    print(f"--- {APP_NAME} v{APP_VERSION} ---")
    print(f"Instance ID: {INSTANCE_ID}")

    if IS_INTERACTIVE_TTY:
        # Get input directory interactively
        input_dir_prompt = input(f"Input directory (default: '{DEFAULT_INPUT_DIR}'): ").strip()
        input_dir = input_dir_prompt or DEFAULT_INPUT_DIR # Use default if empty
        
        # Get keywords interactively
        try:
            keywords_str_prompt = input("Keywords (comma-separated, blank for all): ").strip()
            keywords_str = keywords_str_prompt
        except EOFError: # Handle Ctrl+D or unexpected EOF during input
            logging.warning("EOF received while waiting for keywords input during interactive prompt. Exiting gracefully.")
            print("\nExiting due to unexpected end of input stream.")
            return 0 # Graceful exit
    else: # Non-interactive mode: use arguments
        input_dir = args.input
        keywords_str = args.keywords

    # Process keywords: split, strip, lowercase, remove empty
    keywords = [k.strip().lower() for k in keywords_str.split(',') if k.strip()]
    logging.debug(f"Keywords list for filtering: {keywords}")

    # Validate input directory
    if not os.path.isdir(input_dir):
        logging.critical(f"Input directory '{input_dir}' not found or is not a directory. Please provide a valid path.")
        print(f"❌ Error: Input directory '{os.path.abspath(input_dir)}' not found or is invalid. Please check the path provided.")
        return 1 # Exit with error code

    if IS_INTERACTIVE_TTY: # Provide feedback in interactive mode
        print(f"🔍 Keywords to search: {keywords if keywords else 'ALL (no filter)'}")
        print(f"📁 Output for this instance will be saved to: {os.path.abspath(output_path)}")

    # Load list of already processed files for resume capability
    processed_files_set = load_processed_files(processed_log_path)
    logging.debug(f"Loaded {len(processed_files_set)} previously processed files from log for resume capability.")

    # Scan for relevant files in the input directory (recursive)
    # In addition to .txt files, also include .csv, .json and .jsonl as potential inputs.
    all_target_files: List[str] = []
    logging.info(
        f"Scanning input directory '{input_dir}' for .txt, .csv, .json, and .jsonl files to find potential targets..."
    )
    try:
        # os.walk will traverse the directory and its subdirectories.
        # The onerror argument allows handling of errors during traversal (e.g., permission denied on a subfolder)
        # without stopping the entire scan.
        for root, _, files in os.walk(input_dir, onerror=_walk_error_logger):
            files.sort()  # Process files in a consistent order
            for file_name in files:
                full_file_path = os.path.join(root, file_name)
                # Exclude internal log/output files from being processed as input
                lower_name = file_name.lower()
                # Determine whether this file should be skipped because it is an internal log
                # or one of our own output files. Skip processed_files_*, extractor_errors_*,
                # merge output file, WordPress output file, and our chunked output prefix (filtered_*).
                is_internal_log = lower_name.startswith('processed_files_') or lower_name.startswith('extractor_errors_')
                # Recognize files that are internal outputs: either explicitly named merge files,
                # our WordPress credentials file, files beginning with the output prefix (filtered_),
                # or legacy extracted_lines_* files.
                # Determine if this file is an internal output file. Skip processed_files_* and
                # extractor_errors_* logs. Also skip merged file, legacy extracted_lines_* files,
                # our own chunked output files (filtered_*) and per-CMS output files named
                # like "cmsKey_yyyy-mm-dd-hh-mm.txt".
                is_internal_output = (
                    lower_name.startswith('extracted_lines_')
                    or lower_name.startswith('filtered_')
                    or lower_name == args.merge_file.lower()
                    or lower_name == os.path.basename(WORDPRESS_OUTPUT_FILE).lower()
                    # Skip CMS-specific output files generated by this script
                    # Skip per-CMS output files which now follow the pattern
                    # '<folder>-<timestamp>.txt' where folder is derived from CMS_DIR_MAP.
                    or any(lower_name.startswith(f"{CMS_DIR_MAP.get(cms_key, cms_key).lower()}-") for cms_key in cms_unique_credentials.keys())
                )

                # Accept files ending with .txt, .csv, .json, .jsonl or .xml (case-insensitive).
                # XML files are treated separately for HTTP CMS detection but
                # still collected into the all_target_files list so they can be
                # processed in the main loop.  Internal logs/outputs are
                # excluded.
                if not (is_internal_log or is_internal_output):
                    if (
                        lower_name.endswith('.txt')
                        or lower_name.endswith('.csv')
                        or lower_name.endswith('.json')
                        or lower_name.endswith('.jsonl')
                    ):
                        all_target_files.append(os.path.abspath(full_file_path))
                    elif lower_name.endswith('.xml'):
                        # Burp HTTP history exports use the .xml extension.  Include
                        # them here; they will be processed by a dedicated handler.
                        all_target_files.append(os.path.abspath(full_file_path))
        # Sort all found files for consistent processing order across runs if directory content is the same
        all_target_files.sort()
        logging.info(
            f"Finished scanning. Found {len(all_target_files)} total files matching criteria (excluding internal files)."
        )
        if all_target_files:
            logging.debug(
                f"All found potential input file paths (first few if many): {all_target_files[:5]}"
            )
    except Exception as e:
        # Catch other errors during the setup of os.walk or if _walk_error_logger itself fails critically
        logging.error(
            f"Critical error during input directory scan setup '{input_dir}': {e}", exc_info=True
        )
        print(f"❌ Critical error scanning input directory: {e}")
        return 1  # Exit with error

    # Filter out already processed files
    files_to_process = [f_path for f_path in all_target_files if f_path not in processed_files_set]
    num_found = len(all_target_files)
    num_to_process = len(files_to_process)
    num_skipped_initial = num_found - num_to_process

    if num_found == 0:
        # Inform the user if no eligible input files were located. This message is
        # intentionally generic since multiple extensions are now supported.
        print(f"🟡 No input files matching the supported extensions (.txt, .csv, .json, .jsonl) were found in '{input_dir}'.")
        logging.info("Exiting: No matching input files found to process after scan.")
        return 0
    if num_to_process == 0: # num_found > 0 implicit here
        print(f"✅ All {num_found} file(s) found are already marked as processed in the log.")
        logging.info("Exiting: All found files already processed based on log entries.")
        return 0
    
    # Summarize the number of files discovered and planned for processing. This
    # message dynamically reflects the broadened set of supported file types.
    print(
        f"Found {num_found} total input file(s). {num_skipped_initial} file(s) previously processed (skipped from log). {num_to_process} file(s) scheduled for processing in this run."
    )

    if IS_INTERACTIVE_TTY and _has_working_kb_input:
        print("Press Enter or Space at any time to skip processing the current file.")
    elif IS_INTERACTIVE_TTY: # Interactive but no working keyboard input
        logging.info("Interactive skip feature disabled: Keyboard input functions not fully functional on this system.")

    # --- File Processing Loop ---
    # MODIFIED: unique_lines now stores tuples of (url, user, pass) for deduplication
    unique_lines: Set[Tuple[str, str, str]] = set() 
    processed_in_run = 0 # Count of files successfully processed in this session
    start_time = time.perf_counter() # For ETA calculation and final summary

    # Shared state for inter-thread communication (watchdog, input listener)
    progress_state = {
        'stop_listener': False,      # Signal for input_listener_thread to stop
        'stop_requested': False,     # Signal for current file processing to stop (by watchdog or user)
        'manual_skip_requested': False,
        'watchdog_triggered': False,
        'bytes': 0, 'lines': 0, 'hits': 0, 'file_size': -1,
        'current_file': 'None',      # Basename of the file currently being processed
    }
    logging.debug("Initialized shared progress_state dictionary for inter-thread communication.")

    input_thread = None
    if IS_INTERACTIVE_TTY and _has_working_kb_input:
        input_thread = threading.Thread(target=input_listener_thread, args=(progress_state,), daemon=True)
        input_thread.start()
        logging.debug("Interactive input listener thread started in daemon mode.")
    # No 'else' needed for logging here, covered by earlier IS_INTERACTIVE_TTY checks.

    output_file = None  # Initialize output writer for combined output
    # Initialize per-CMS output files and load existing credentials
    try:
        # Determine a timestamp string for naming CMS-specific output files. Use
        # day-month-year-hour-minute as requested (e.g. 08-04-2025-18-45).
        timestamp_str = datetime.now().strftime("%d-%m-%Y-%H-%M")
        # Ensure the keyword output directory exists before creating files
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        # Prepare the base directory for CMS-specific outputs (cms-detect)
        # The directory structure is script_dir/cms-detect/<cms> and will be
        # created on demand.
        try:
            script_dir_local = script_dir
        except Exception:
            script_dir_local = os.getcwd()
        cms_detect_dir = os.path.join(script_dir_local, 'cms-detect')
        # Iterate through each CMS identifier and prepare its output file
        for cms_key in cms_unique_credentials.keys():
            # Map CMS key to folder/file name
            cms_dir_name = CMS_DIR_MAP.get(cms_key, cms_key)
            cms_dir_path = os.path.join(cms_detect_dir, cms_dir_name)
            # Ensure directory exists
            os.makedirs(cms_dir_path, exist_ok=True)
            # Define file name pattern cmsName-date-time.txt
            cms_filename = f"{cms_dir_name}-{timestamp_str}.txt"
            cms_file_path = os.path.join(cms_dir_path, cms_filename)
            # Load existing credentials for resume (if any files exist in this folder)
            try:
                if os.path.isdir(cms_dir_path):
                    for existing in os.listdir(cms_dir_path):
                        ename = existing.lower()
                        # Skip the HTTP detection results.txt file
                        if ename == 'results.txt':
                            continue
                        # Match pattern cmsName-....txt
                        if ename.startswith(f"{cms_dir_name.lower()}-") and ename.endswith('.txt'):
                            resume_file = os.path.join(cms_dir_path, existing)
                            try:
                                with open(resume_file, 'r', encoding='utf-8', errors='ignore') as f_cms:
                                    for line in f_cms:
                                        parsed = parse_output_line(line)
                                        if parsed:
                                            cms_unique_credentials[cms_key].add(parsed)
                            except Exception as resume_read_exc:
                                logging.error(
                                    f"Error loading existing CMS credentials from '{resume_file}': {resume_read_exc}",
                                    exc_info=True,
                                )
                # Open the file for appending and assign to cms_output_files
                cms_output_files[cms_key] = open(cms_file_path, 'a', encoding='utf-8', newline='\n')
                logging.info(f"Opened {cms_key.capitalize()} output file for appending: {cms_file_path}")
            except Exception as cms_open_exc:
                logging.error(
                    f"Could not open or read output file for CMS '{cms_key}' at '{cms_file_path}': {cms_open_exc}. Credentials for this CMS will not be logged.",
                    exc_info=True,
                )
                cms_output_files[cms_key] = None

        # MODIFIED: Load existing credential tuples from all existing output chunks (if resuming).
        # When using ChunkedWriter, multiple output files may exist for a single instance. To
        # correctly resume, scan for any files starting with the base name of the
        # intended output path and ending with the same extension. This ensures that
        # previously written chunks contribute to the in-memory deduplication set.
        try:
            base_no_ext, ext = os.path.splitext(output_path)
            output_dir_name = os.path.dirname(output_path) or '.'
            base_prefix = os.path.basename(base_no_ext)
            existing_chunk_files: List[str] = []
            if os.path.isdir(output_dir_name):
                for _fname in os.listdir(output_dir_name):
                    lower_fname = _fname.lower()
                    # Match files that start with the base prefix and share the same extension
                    if lower_fname.startswith(base_prefix.lower()) and lower_fname.endswith(ext.lower()):
                        existing_chunk_files.append(os.path.join(output_dir_name, _fname))
            # Read credentials from each discovered output file
            for resume_path in existing_chunk_files:
                if os.path.getsize(resume_path) > 0:
                    logging.info(
                        f"Loading existing unique credentials from output file '{os.path.basename(resume_path)}' for resume."
                    )
                    try:
                        with open(resume_path, 'r', encoding='utf-8', errors='ignore') as f_resume:
                            for line_str in f_resume:
                                parsed = parse_output_line(line_str)
                                if parsed:
                                    unique_lines.add(parsed)
                        logging.info(
                            f"Loaded credentials from '{os.path.basename(resume_path)}'. Current total unique credentials in memory: {len(unique_lines):,}."
                        )
                    except Exception as resume_e:
                        logging.error(
                            f"Error loading existing output file '{resume_path}' for resume: {resume_e}",
                            exc_info=True,
                        )
        except Exception as e:
            logging.error(
                f"Unexpected error while scanning for existing output chunk files for resume: {e}",
                exc_info=True,
            )


        # Open the main output file (or chunk) for this instance in append mode.
        # Use the ChunkedWriter to automatically rotate when a file exceeds the configured size.
        try:
            # Ensure directory exists before opening file
            os.makedirs(os.path.dirname(output_path), exist_ok=True)
            # Determine the highest existing chunk index to resume writing into the last chunk.
            base_no_ext, ext = os.path.splitext(output_path)
            highest_index = 1
            # Scan the output directory for existing chunks matching the pattern
            out_dirname = os.path.dirname(output_path) or '.'
            base_prefix = os.path.basename(base_no_ext)
            if os.path.isdir(out_dirname):
                for _fname in os.listdir(out_dirname):
                    lower_fname = _fname.lower()
                    if lower_fname.startswith(base_prefix.lower()) and lower_fname.endswith(ext.lower()):
                        # Determine index: default to 1 for base file, otherwise parse suffix
                        if _fname == os.path.basename(output_path):
                            idx = 1
                        else:
                            # Attempt to extract index from filename after the underscore
                            # Example: filtered_xxx_3.txt -> index 3
                            name_without_ext = _fname[:-len(ext)] if ext else _fname
                            # Split on last underscore to get numeric suffix
                            parts = name_without_ext.rsplit('_', 1)
                            if len(parts) == 2 and parts[1].isdigit():
                                idx = int(parts[1])
                            else:
                                idx = 1
                        if idx > highest_index:
                            highest_index = idx
            # Instantiate the chunked writer starting from the highest existing index
            output_file = ChunkedWriter(output_path, MAX_OUTPUT_FILE_SIZE_BYTES, start_index=highest_index)
            logging.debug(
                f"Successfully opened chunked output writer '{output_path}' starting at chunk index {highest_index}."
            )
        except Exception as e:
            logging.critical(
                f"FATAL ERROR: Failed to initialize output writer for '{output_path}': {e}. Cannot proceed.",
                exc_info=True,
            )
            print(
                f"❌ Fatal Error: Could not initialize output writer '{os.path.abspath(output_path)}' for writing: {e}. Exiting."
            )
            exit_flag = True  # Signal to stop everything
            return 1  # Exit with error

        # Setup progress bars
        pbar_overall_desc = f"Overall Progress (Instance: {INSTANCE_ID[:8]})"
        
        # Main tqdm context for overall progress
        with tqdm(total=num_to_process, desc=pbar_overall_desc, dynamic_ncols=True, position=0, leave=True, disable=not IS_INTERACTIVE_TTY) as pbar_overall:
            # Inner tqdm context for individual file progress
            with tqdm(total=1, desc="Initializing...", dynamic_ncols=True, position=1, leave=False, disable=not IS_INTERACTIVE_TTY) as pbar_file:
                pbar_overall.set_postfix_str(f"Files: {processed_in_run}/{num_to_process} | Unique (mem): {len(unique_lines):,}", refresh=True)

                for file_idx, file_path in enumerate(files_to_process):
                    if exit_flag: # Check for global interrupt signal
                        logging.info("Shutdown requested (exit_flag is True). Breaking main file processing loop.")
                        break

                    # Update ETA periodically
                    if file_idx > 0 and (file_idx + 1) % 10 == 0: # Every 10 files
                        elapsed_iter = time.perf_counter() - start_time
                        avg_time_per_file = elapsed_iter / (file_idx + 1) # Avg time for files processed so far
                        remaining_files = num_to_process - (file_idx + 1)
                        eta_seconds = avg_time_per_file * remaining_files if avg_time_per_file > 0 else 0
                        eta_str = f"{eta_seconds/60:.1f}m" if eta_seconds > 60 else f"{eta_seconds:.0f}s"
                        pbar_overall.set_postfix_str(f"ETA: {eta_str} ({avg_time_per_file:.1f}s/file) | Unique (mem): {len(unique_lines):,}", refresh=False)

                    # Reset file-specific flags in progress_state
                    progress_state['stop_requested'] = False
                    progress_state['manual_skip_requested'] = False
                    progress_state['watchdog_triggered'] = False
                    progress_state['current_file'] = os.path.basename(file_path)
                    logging.debug(f"Main loop starting processing for file '{file_path}'. Calling process_file...")

                    # Determine file extension and handle HTTP history files separately
                    try:
                        _, file_ext = os.path.splitext(file_path)
                        ext_lower = file_ext.lower()
                    except Exception:
                        ext_lower = ''

                    if ext_lower == '.xml':
                        # XML files are treated as Burp Suite HTTP history exports.  Use
                        # dedicated processing to detect CMS evidence from HTTP traffic.
                        logging.info(f"Processing HTTP history file: '{os.path.basename(file_path)}'")
                        process_http_history_file(file_path, cms_http_records, cms_http_counts)
                        # Mark as processed
                        log_processed_file(processed_log_path, file_path)
                        processed_in_run += 1
                        # Update progress bar for the processed file
                        pbar_overall.update(1)
                        # Maintain postfix with current counts; unique_lines unaffected
                        pbar_overall.set_postfix_str(
                            f"Files: {processed_in_run}/{num_to_process} | Unique (mem): {len(unique_lines):,}",
                            refresh=True
                        )
                        # Skip standard text processing
                        continue

                    # Process the current non-XML file
                    # Pass None for wordpress_output_file since CMS-specific outputs
                    # are handled by cms_output_files and cms_unique_credentials.
                    lines_added_from_file = process_file(
                        file_path=file_path,
                        keywords=keywords,
                        output_file=output_file,
                        wordpress_output_file=None,
                        unique_lines=unique_lines,  # Passed by reference, modified by process_file
                        pbar_file=pbar_file if IS_INTERACTIVE_TTY else None,  # Pass None if not interactive
                        progress_state=progress_state
                    )
                    logging.debug(f"process_file for '{os.path.basename(file_path)}' returned result: {lines_added_from_file}")

                    # Handle result of file processing
                    if lines_added_from_file != -1: # -1 indicates error or skip
                         manual_skipped_during_file = progress_state.get('manual_skip_requested', False)
                         watchdog_triggered_during_file = progress_state.get('watchdog_triggered', False)

                         if not manual_skipped_during_file and not watchdog_triggered_during_file:
                            # Successfully processed without manual skip or watchdog intervention
                            log_processed_file(processed_log_path, file_path) # Log as processed
                            processed_in_run += 1
                            logging.info(f"Successfully completed processing file: '{os.path.basename(file_path)}'. Added {lines_added_from_file:,} unique credentials (total unique tuples in memory: {len(unique_lines):,}).")
                         elif manual_skipped_during_file:
                              logging.info(f"File '{os.path.basename(file_path)}' processing manually skipped by user.")
                         elif watchdog_triggered_during_file:
                              logging.info(f"File '{os.path.basename(file_path)}' processing stalled and aborted by watchdog.")
                         # File was handled (processed, skipped, or watchdog) - update overall progress
                         pbar_overall.update(1)
                         pbar_overall.set_postfix_str(
                             f"Files: {processed_in_run}/{num_to_process} | Unique (mem): {len(unique_lines):,}", # len(unique_lines) is now count of tuples
                             refresh=True
                         )
                    else: # lines_added_from_file == -1, meaning an error occurred in process_file
                        logging.error(f"Processing of file '{os.path.basename(file_path)}' failed or was aborted (process_file returned -1). File will be re-attempted on a next run if not logged.")
                        # Do not log to processed_files.log if it failed, so it can be retried.
                        pbar_overall.update(1) # Still update overall progress as one file attempt is done
                        pbar_overall.set_postfix_str(f"Files: {processed_in_run}/{num_to_process} | ❌ Error/Skipped: {os.path.basename(file_path)[:15]}...", refresh=True) # Truncate long names
                    
                    # Reset these for the next iteration, though process_file also resets them
                    progress_state['manual_skip_requested'] = False
                    progress_state['watchdog_triggered'] = False

    except KeyboardInterrupt: # Should be caught by SIGINT handler, but as a fallback
        logging.warning("KeyboardInterrupt exception caught in main loop try block. Setting exit_flag.")
        # Avoid double printing if handle_sigint already printed
        if not exit_flag: # Check if flag was already set by handler
            print("\n⚠️ Process interrupted by KeyboardInterrupt. Saving current progress...")
        exit_flag = True
    except Exception as e: # Catch-all for unexpected critical errors in main loop
        logging.critical(f"A critical, unexpected error occurred in the main loop during file iteration: {e}. Script must stop.", exc_info=True)
        print(f"\n❌ A critical unexpected error occurred: {e}. Script is stopping.")
        exit_flag = True
    finally:
        logging.info("Main processing loop finished or interrupted. Executing cleanup procedures.")
        if output_file and not output_file.closed: # Ensure file is closed
            try:
                output_file.close()
                logging.debug("Main output file handle closed in finally block.")
            except Exception as e:
                logging.error(f"Error closing main output file '{output_path}' in finally block: {e}", exc_info=True)
        
        # Close all per-CMS output files (including WordPress) if they were opened
        # Loop through the cms_output_files dictionary and close each handle
        for _cms_key, _cms_handle in list(cms_output_files.items()):
            if _cms_handle and not _cms_handle.closed:
                try:
                    _cms_handle.close()
                    logging.debug(f"{_cms_key.capitalize()} output file handle closed in finally block.")
                except Exception as e_close_cms:
                    logging.error(
                        f"Error closing output file for CMS '{_cms_key}' in finally block: {e_close_cms}",
                        exc_info=True,
                    )

        # Stop and join input listener thread if it's running
        if input_thread and input_thread.is_alive():
            logging.debug("Signaling input listener thread to stop via 'stop_listener' flag.")
            progress_state['stop_listener'] = True # Signal thread to exit its loop
            try:
                input_thread.join(timeout=2) # Wait for thread to finish
                if input_thread.is_alive():
                    logging.warning(f"Input listener thread did not terminate cleanly after signal and timeout.")
                else:
                     logging.debug("Input listener thread joined successfully in finally block.")
            except Exception as join_e:
                logging.error(f"Error joining input listener thread in finally block: {join_e}", exc_info=True)
        
        
        # Finalize the output file(s) for this instance (sort and deduplicate)
        # This is done regardless of interruption to save progress. When using
        # ChunkedWriter, multiple chunk files may exist; each must be
        # individually deduplicated and sorted. The cumulative count is
        # returned for summary purposes.
        final_count_after_run_instance_file = 0
        try:
            # If output_file is a ChunkedWriter, iterate over its chunk_paths
            if hasattr(output_file, 'chunk_paths') and isinstance(getattr(output_file, 'chunk_paths'), list):
                for _chunk_path in output_file.chunk_paths:
                    count = sort_and_deduplicate(_chunk_path)
                    final_count_after_run_instance_file += count
                    logging.debug(
                        f"Final unique lines in '{os.path.basename(_chunk_path)}' after sort/dedupe: {count:,}."
                    )
            else:
                # Fallback: single output file, dedupe once
                final_count_after_run_instance_file = sort_and_deduplicate(output_path)
                logging.debug(
                    f"Final unique lines in '{os.path.basename(output_path)}' after sort/dedupe: {final_count_after_run_instance_file:,}."
                )
        except Exception as dedupe_e:
            logging.error(
                f"Unexpected error during final sort/dedupe of output files: {dedupe_e}",
                exc_info=True,
            )

        # Perform merge operation if requested and not interrupted by error/SIGINT
        merged_file_full_path = os.path.join(output_dir, args.merge_file)
        merged_count = -1 # Initialize to indicate not run or failed

        if args.merge and not exit_flag: # Only merge if requested and no prior critical error/interrupt
            logging.info("Merge operation initiated as requested (script not interrupted before cleanup).")
            merged_count = merge_output_files(output_dir, OUTPUT_FILE_TEMPLATE, args.merge_file)
            if merged_count >= 0: # merge_output_files returns count or 0 for empty/error
                logging.info(f"Merge operation completed. Final merged file '{os.path.basename(merged_file_full_path)}' contains {merged_count:,} unique lines.")
                print(f"✅ Merge operation successful: Created/updated '{os.path.basename(merged_file_full_path)}' with {merged_count:,} unique lines.")
            else: # Should ideally be 0 if no lines, but -1 could be custom error code if changed
                 logging.error(f"Merge operation reported an error or resulted in zero lines (returned {merged_count}). Check logs.")
                 print(f"❌ Merge operation encountered an error or resulted in zero lines.")
        elif args.merge and exit_flag: # Merge requested but script was interrupted
             logging.warning("Merge operation skipped because the script was interrupted or encountered an error during processing.")
             print(f"⚠️ Merge operation skipped due to script interruption or error.")

        # --- Summary Output ---
        elapsed = time.perf_counter() - start_time
        # Determine the most relevant final count to report
        reported_final_count = final_count_after_run_instance_file # Default to instance file count

        if args.merge and not exit_flag and merged_count >= 0: # If merge ran and was successful (or 0 lines)
            reported_final_count = merged_count
            logging.debug(f"Summary total count ({reported_final_count:,}) taken from successful merge operation result.")
        # Fallback for merge if merged_count wasn't correctly set but file exists and has content (less ideal)
        elif args.merge and not exit_flag and os.path.exists(merged_file_full_path) and os.path.getsize(merged_file_full_path) > 0 and merged_count < 0:
             try: # Attempt to count lines in the merged file directly
                with open(merged_file_full_path, 'r', encoding='utf-8', errors='ignore') as f_merged_count:
                    reported_final_count = sum(1 for line in f_merged_count if line.strip())
                logging.debug(f"Summary total count ({reported_final_count:,}) taken from final merged file '{os.path.basename(merged_file_full_path)}' (fallback count).")
             except Exception as e_count:
                logging.error(f"Could not accurately count lines in merged file '{merged_file_full_path}' for summary display: {e_count}. Reporting count from this instance's output file ({final_count_after_run_instance_file:,}) instead.", exc_info=True)
        elif args.merge and not exit_flag and os.path.exists(merged_file_full_path) and os.path.getsize(merged_file_full_path) == 0:
             # If merge file exists but is empty (and merge ran without error signal)
             reported_final_count = 0
             logging.debug("Summary total count is 0: Merged file exists but is empty.")

        # After completing deduplication and optional merge operations, write
        # HTTP-based CMS detection results (if any were collected) into the
        # output directory.  This ensures that CMS-specific folders and
        # summary files are generated regardless of whether text extraction
        # produced any credentials.  The write is only attempted once per run.
        try:
            if cms_http_records:
                # Write HTTP detection results into the cms-detect directory
                try:
                    script_dir_local = script_dir
                except Exception:
                    script_dir_local = os.getcwd()
                cms_detect_dir = os.path.join(script_dir_local, 'cms-detect')
                write_http_detection_results(cms_http_records, cms_http_counts, cms_detect_dir)
                logging.info("HTTP-based CMS detection results written successfully.")
        except Exception as http_write_e:
            logging.error(f"Error writing HTTP detection results: {http_write_e}", exc_info=True)

        # After completing deduplication and optional merge operations, write
        # the list of unique WordPress installation domains (with trailing slashes)
        # into a dedicated file.  This file contains only the base URLs (scheme + host
        # + subfolder) for each WordPress site detected during processing.
        try:
            if wordpress_domains_set:
                os.makedirs(BASE_OUTPUT_DIR, exist_ok=True)
                with open(WORDPRESS_DOMAIN_FILE, 'w', encoding='utf-8', newline='\n') as f_wp:
                    for base_url in sorted(wordpress_domains_set):
                        f_wp.write(base_url + '\n')
                # Provide feedback to the user if any files were processed
                if num_found > 0:
                    print(f"📑 WordPress domain list saved to: {os.path.abspath(WORDPRESS_DOMAIN_FILE)}")
                logging.info(f"WordPress domain list written with {len(wordpress_domains_set):,} entries.")
        except Exception as wp_e:
            logging.error(f"Error writing WordPress domain list: {wp_e}", exc_info=True)


        if num_found > 0:  # Only print summary if files were initially found
            print(f"\n--- Processing Summary ---")
            # Reflect the broadened search to multiple file types
            print(f"✓ Total input files found (potential inputs): {num_found}")
            print(f"✓ Files skipped due to resume log: {num_skipped_initial}")
            print(f"✓ Files successfully completed this run: {processed_in_run} (of {num_to_process} planned)")
            # The reported_final_count is derived from the deduplication/merge process
            print(f"✓ Final total unique lines extracted/merged: {reported_final_count:,}")
            print(f"✓ In-memory unique credential tuples collected this run: {len(unique_lines):,}")
            print(f"✓ Total time elapsed: {elapsed:.2f}s")
            
            if exit_flag:
                status_message = "Processing was interrupted."
                # Add more specific details if available from progress_state
                if progress_state.get('watchdog_triggered', False):
                     status_message += " (Possible watchdog stall detection)."
                # Note: manual_skip_requested applies to a single file, not global interruption
                if args.merge: status_message += " Merge operation may have been skipped or incomplete."
                print(f"⚠️ {status_message}")
            else:
                print(f"🏁 Extraction job completed successfully.")

            # Information about output files
            if reported_final_count > 0:
                # If we used a ChunkedWriter, display the paths to each non-empty sorted output file
                if hasattr(output_file, 'chunk_paths') and isinstance(output_file.chunk_paths, list):
                    for _cp in output_file.chunk_paths:
                        if os.path.exists(_cp) and os.path.getsize(_cp) > 0:
                            print(f"📄 This instance's sorted output saved to: {os.path.abspath(_cp)}")
                else:
                    # Fallback for single output file
                    if final_count_after_run_instance_file > 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0:
                        print(f"📄 This instance's sorted output saved to: {os.path.abspath(output_path)}")

                if args.merge and not exit_flag and merged_count > 0 and os.path.exists(merged_file_full_path) and os.path.getsize(merged_file_full_path) > 0:
                    print(f"📄 All relevant files merged into: {os.path.abspath(merged_file_full_path)}")
            else:  # No lines reported
                print(
                    f"📄 No unique lines were extracted/merged that met criteria, or deduplication resulted in zero lines. Output file(s) may be empty or not created."
                )
                # Optional: cleanup empty files. Remove all empty chunk files and merge file if they exist.
                # First, handle instance's chunk files if using ChunkedWriter
                if hasattr(output_file, 'chunk_paths') and isinstance(output_file.chunk_paths, list):
                    for _cp in output_file.chunk_paths:
                        if os.path.exists(_cp) and os.path.getsize(_cp) == 0:
                            try:
                                os.remove(_cp)
                                logging.info(f"Removed empty output file: {_cp}")
                            except Exception as e_rm:
                                logging.warning(f"Could not remove empty output file {_cp}: {e_rm}")
                else:
                    # Fallback: single output file
                    if os.path.exists(output_path) and os.path.getsize(output_path) == 0:
                        try:
                            os.remove(output_path)
                            logging.info(f"Removed empty output file: {output_path}")
                        except Exception as e_rm:
                            logging.warning(f"Could not remove empty output file {output_path}: {e_rm}")

                # Then handle merge file if applicable
                if args.merge and os.path.exists(merged_file_full_path) and os.path.getsize(merged_file_full_path) == 0:
                    try:
                        os.remove(merged_file_full_path)
                        logging.info(f"Removed empty output file: {merged_file_full_path}")
                    except Exception as e_rm:
                        logging.warning(f"Could not remove empty output file {merged_file_full_path}: {e_rm}")
                            
    # Return exit code
    if exit_flag: # If script was interrupted or had a critical error
        logging.info("Script exiting with error code 1 due to interruption or error detected.")
        return 1
    else:
        logging.info("Script exiting successfully with code 0.")
        return 0

if __name__ == "__main__":
    # Ensure terminal settings are restored on POSIX, even if main() raises an unhandled exception
    # This is a fallback, as atexit.register(_restore_normal_input) should also handle it.
    try:
        sys.exit(main())
    finally:
        if sys.platform != 'win32' and _termios_old_settings is not None: # Check if settings were ever captured
            logging.debug("Ensuring terminal settings are restored in __main__ finally block (if changed).")
            _restore_normal_input()