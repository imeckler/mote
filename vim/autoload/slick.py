import vim
import threading
import subprocess
import json
import os.path

log    = open(os.path.join(os.path.expanduser('~'), 'slicklog'), 'w', 0)
reader = None

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

def replace(span, path, s):
  b = find(lambda b: b.name == path, vim.buffers)
  if b is None: return
  ((l0,c0), (l1,c1)) = span

  lines     = s.splitlines()
  log.write('lines: ' + repr(lines) + '\n')
  log.write('span: ' + repr(span) + '\n')
  tail      = b[l1 - 1][c1:]
  lines[-1] = lines[-1] + tail

  b[l0 - 1] = b[l0 - 1][:c0 - 1] + lines[0]
  b[l0:l1] = lines[1:]


class SlickProcess:
  def __init__(self):
    self.pipe        = None
    self.info_window = None

  # returns a bool. False = stop, True = keep going

  def set_info_window(self, s):
    info_window = self.get_info_window()
    del info_window.buffer[:]
    for line in s.splitlines():
      info_window.buffer.append(line)

  def handle(self, s):
    try:
      msg = json.loads(s)
    except:
      return False

    # except:
    #   print ("No bueno")
    #   return True

    if msg[0] == 'Ok':
      pass

    elif  msg[0] == 'Error':
      self.set_info_window(msg[1])

    elif msg[0] == 'SetInfoWindow':
      log.write('setting info window\n')
      log.write('fo: ' + msg[1] + '\n')
      self.set_info_window(msg[1])

    elif msg[0] == 'SetCursor':
      (line, col) = msg[1]
      vim.current.window.cursor = (line, col - 1)

    elif msg[0] == 'Replace':
      replace(msg[1], msg[2], msg[3])

    elif msg[0] == 'Stop':
      return False

    return True

  def _send_message(self, x):
    s = json.dumps(x) + '\n'
    log.write('_send_message: ' + s)
    if self.pipe.returncode == None:
      self.pipe.stdin.write(s)
    else:
      log.write('send message: return code not none. heres stderr\n')


  def start(self):
    try:
      self.pipe = subprocess.Popen(['slick'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=log) #TODO:debug
    except OSError as e:
      raise e

  def send_stop(self):
    self._send_message(['SendStop'])

  def get_info_window(self):
    if self.info_window == None or not self.info_window.valid:
      self.info_window = vim.windows[int(vim.eval('slick#CreateInfoWindow()')) - 1]
    return self.info_window

  def load(self, path):
    log.write('load method\n')
    self._send_message(['Load', path])

  def enter_hole(self):
    self._send_message(['EnterHole', get_client_state()])

  def get_env(self):
    self._send_message(['GetEnv', get_client_state()])

  def get_type(self, expr):
    self._send_message(['GetType', expr])

slick_process = None
def get_slick_process():
  global slick_process

  if not slick_process:
    slick_process = SlickProcess()
    slick_process.start()

  return slick_process

def wait_for_messages():
  keep_going = True

  while keep_going:
    slick = get_slick_process()
    if slick.pipe.returncode == None:
      log.write('returncode was none\n')
      s = slick.pipe.stdout.readline()

      log.write('got message: ' + s + '\n')
      keep_going = slick.handle(s)
    else:
      log.write('returncode was not none\n')
      break

def start():
  global reader
  reader = threading.Thread(target=wait_for_messages)
  reader.start()
  log.write('called start\n')

def stop():
  get_slick_process().send_stop()

def load_current_file():
  log.write('called load\n')
  get_slick_process().load(vim.current.buffer.name)

def get_env():
  get_slick_process().get_env()

def get_type(expr):
  get_slick_process().get_type(expr)

def enter_hole():
  get_slick_process().enter_hole()

def next_hole():
  get_slick_process()._send_message(['NextHole', get_client_state()])

def prev_hole():
  get_slick_process()._send_message(['PrevHole', get_client_state()])

def case_further(var):
  get_slick_process()._send_message(['CaseFurther', var, get_client_state()])

