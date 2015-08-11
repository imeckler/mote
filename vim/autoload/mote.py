import vim
import threading
import subprocess
import json
import os.path
import select
import re

# This doesn't work in vim 7.3. Window doesn't have a "valid" attribute,
# among other things

# Need to kill processes properly. If I open two motes then they don't
# get killed correctly

log    = open(os.path.join(os.path.expanduser('~'), '.motelog'), 'w', 0)
reader = None

# returns (x, s') where x is the result and s' is the remaining string
def parse_functor(s):
  s = s.strip()
  if s[0] == '{':
    (x, s1) = parse_functor(s[1:])
    if s1[0] == '}':
      return (x, s1[1:])
    else:
      raise Exception('Bad parse')
  else:
    [x, rest] = s.split(' ', 1)
    return (x, rest)

def parse_functor_list(s):
  res = []
  while s:
    (x, s1) = parse_functor(s)
    res.push(x)
    s = s1
  return x

def get_client_state():
  (l, c)      = vim.current.window.cursor
  path        = vim.current.buffer.name # vim.eval("expand('%:p')"),
  info_window = None
  return {'path': path, 'cursorPos' : [l, c + 1]}

def find(p, xs):
  for x in xs:
    if p(x):
      return x
  return None

def insert(pos, path, s):
  b = find(lambda b: b.name == path, vim.buffers)
  if b is None: return

  s = s.encode('utf-8')
  lines = s.splitlines()
  if not lines: return
  
  (l0, c0) = pos
  l0 -= 1
  c0 -= 1

  l0start = b[l0][:c0]
  l0end   = b[l0][c0:]
  b[l0]   = l0start + lines[0]
  b.append(lines[1:], l0 + 1)

# pretty sure this is wrong
def replace(span, path, s):
  s = s.encode('utf-8')
  b = find(lambda b: b.name == path, vim.buffers)
  if b is None: return
  ((l0,c0), (l1,c1)) = span

  lines     = s.splitlines()
  log.write('lines: ' + repr(lines) + '\n')
  log.write('span: ' + repr(span) + '\n')
  if l0 == l1:
    b[l0 - 1] = b[l0 - 1][:c0 - 1] + lines[0] + b[l0 - 1][c1 - 1:]
    b.append(lines[1:], l0 - 1)
  else:
    tail      = b[l1 - 1][c1:]
    lines[-1] = lines[-1] + tail

    b[l0 - 1] = b[l0 - 1][:c0 - 1] + lines[0]
    b[l0:l1] = lines[1:]


def synchronous(cmd):
  def sync_cmd(self, *args):
    cmd(self, *args)
    s = self.pipe.stdout.readline()
    log.write('got message: ' + s + '\n')
    return self.handle(s)
  return sync_cmd

class MoteProcess:
  def __init__(self):
    self.pipe             = None
    self.info_window      = None
    self.displaying_error = False

  # returns a bool. False = stop, True = keep going

  def append_to_info_window(self, s):
    info_window = self.get_info_window()
    info_window.buffer.append(s.splitlines())

  def set_info_window(self, s):
    info_window = self.get_info_window()
    log.write('in set info window\n')
    #del info_window.buffer[:]
    log.write('set buffer\n')
    info_window.buffer[:] = s.encode('utf-8').splitlines()

  def handle(self, s):
    try:
      msg = json.loads(s)
    except:
      return False

    if msg[0] == 'Ok':
      pass

    elif  msg[0] == 'Error':
      self.displaying_error = True
      self.set_info_window(msg[1])

    elif msg[0] == 'SetInfoWindow':
      log.write('setting info window\n')
      log.write('fo: ' + msg[1] + '\n')
      self.displaying_error = False
      self.set_info_window(msg[1])

    elif msg[0] == 'SetCursor':
      (line, col) = msg[1]
      vim.current.window.cursor = (line, col - 1)

    elif msg[0] == 'Replace':
      replace(msg[1], msg[2], msg[3])

    elif msg[0] == 'Stop':
      return False

    elif msg[0] == 'Insert':
      insert(msg[1], msg[2], msg[3])

    return True

  def _send_message_dont_wait(self, x):
    s = json.dumps(x) + '\n'
    log.write('_send_message_dont_wait: ' + s)
    if self.pipe.returncode == None:
      self.pipe.stdin.write(s)
      return True
    else:
      return False

  # synchronous for now.
  def _send_message(self, x):
    s = json.dumps(x) + '\n'
    log.write('_send_message: ' + s)
    if self.pipe.returncode == None:
      self.pipe.stdin.write(s)
      s = self.pipe.stdout.readline()
      log.write('got message: ' + s + '\n')
      return self.handle(s)

      # On load, mote may send multiple messages due to errors.
      # Need some way of handling that. The below doesn't work.

      #keepgoing = self.handle(s)
      #while select.select([self.pipe.stdin], [], [], 0.0)[0]:
      #  s = self.pipe.stdin.readline()
      #  log.write('load got: ' + s + '\n') 
      #  keepgoing = keepgoing and self.handle(s)
      #return keepgoing

    else:
      log.write('send message: return code not none. heres stderr\n')

#  def _send_message(self, x):
#    s = json.dumps(x) + '\n'
#    log.write('_send_message: ' + s)
#    if self.pipe.returncode == None:
#      self.pipe.stdin.write(s)
#    else:
#      log.write('send message: return code not none. heres stderr\n')


  def start(self):
    try:
      self.pipe = subprocess.Popen(['mote'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=log) #TODO:debug
    except OSError as e:
      raise e

  def send_stop(self):
    self._send_message(['SendStop'])

  def get_info_window(self):
    if self.info_window == None or not window_is_valid(self.info_window):
      # why did I get invalid expression on this?
      self.info_window = vim.windows[int(vim.eval('mote#CreateInfoWindow()')) - 1]
    return self.info_window

  def load(self, path):
    log.write('load method\n')
    self._send_message(['Load', path])

  def enter_hole(self):
    self._send_message(['EnterHole', get_client_state()])

  def get_env(self):
    hole_info_options = {
      'sendOutputAsData' : False,
      'withSuggestions' : False }
    self._send_message(['GetHoleInfo', get_client_state(), hole_info_options])

  def get_type(self, expr):
    self._send_message(['GetType', expr])

def window_is_valid(w):
  try:
    _ = w.buffer
    return True
  except:
    return False

mote_process = None
def get_mote_process():
  global mote_process

  if not mote_process:
    mote_process = MoteProcess()
    mote_process.start()

  return mote_process

def wait_for_messages():
  keep_going = True

  while keep_going:
    mote = get_mote_process()
    if mote.pipe.returncode == None:
      log.write('returncode was none\n')
      s = mote.pipe.stdout.readline()

      log.write('got message: ' + s + '\n')
      keep_going = mote.handle(s)
    else:
      log.write('returncode was not none\n')
      break

def start():
  global reader
  #reader = threading.Thread(target=wait_for_messages)
  #reader.start()
  #log.write('called start\n')

def stop():
  get_mote_process().send_stop()

def load_current_file():
  log.write('called load\n')
  get_mote_process().load(vim.current.buffer.name)

def get_env():
  get_mote_process().get_env()

def get_type(expr):
  get_mote_process().get_type(expr)

def enter_hole():
  get_mote_process().enter_hole()

def next_hole():
  get_mote_process()._send_message(['NextHole', get_client_state()])

def prev_hole():
  get_mote_process()._send_message(['PrevHole', get_client_state()])

def case_further(var):
  get_mote_process()._send_message(['CaseFurther', var, get_client_state()])

def case_on(expr):
  get_mote_process()._send_message(['CaseOn', expr, get_client_state()])

def refine(expr):
  get_mote_process()._send_message(['Refine', expr, get_client_state()])

def search(n, ty):
  get_mote_process()._send_message(['Search', n, ty])

