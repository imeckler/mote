import vim
import threading
import subprocess
import json

slick_path  = '/home/izzy/prog/slick/dist/build/slick/slick'
log         = open('/home/izzy/slicklog', 'w', 0)
reader      = None

def get_client_state():
  (l, c)      = vim.current.window.cursor
  path        = vim.current.buffer.name # vim.eval("expand('%:p')"),
  info_window = None
  return {'path': path, 'cursorPos' : [l, c + 1]}

class SlickProcess:
  def __init__(self):
    self.pipe        = None
    self.info_window = None

  # returns a bool. False = stop, True = keep going
  def handle(self, msg):
    if msg[0] == 'Ok':
      pass

    elif  msg[0] == 'Error':
      print (msg[1])

    elif msg[0] == 'SetInfoWindow':
      log.write('setting info window\n')
      log.write('fo: ' + msg[1] + '\n')
      info_window = self.get_info_window()
      del info_window.buffer[:]
      for line in msg[1].splitlines():
        info_window.buffer.append(line)

    elif msg[0] == 'Stop':
      return False

    return True

  def _send_message(self, x):
    s = json.dumps(x) + '\n'
    self.pipe.stdin.write(s)
    log.write('_send_message: ' + s)

  def start(self):
    try:
      self.pipe = subprocess.Popen([slick_path], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    except OSError as e:
      print ('hi')
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

    s = slick.pipe.stdout.readline()

    log.write('got message: ' + s + '\n')
    keep_going = slick.handle(json.loads(s))

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

def enter_hole():
  get_slick_process().enter_hole()

