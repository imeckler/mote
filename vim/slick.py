from ws4py.client.threadedclient import WebSocketClient
#import vim


slick_path = '/home/izzy/prog/slick/dist/build/slick/slick'

def get_client_state():
  (l, c)      = vim.current.window.cursor
  path        = vim.current.buffer.name # vim.eval("expand('%:p')"),
  info_window = None
  return {'path': path, 'cursorPos' : [l, c]}

class SlickProcess:
  def __init__(self):
    self.pipe        = None
    self.info_window = None

  def start(self):
    try:
      self.pipe = subprocess.Popen([slick_path], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    except OSError as e:
      print ('hi')
      raise e

  def get_info_window(self):
    if self.info_window == None or not self.info_window.valid:
      self.info_window = vim.windows[vim.eval('slick#CreateInfoWindow')]
    return self.info_window

  def load(self, path):
    json.dump(['Load', path], self.pipe.stdin)
    result = json.loads(self.pipe.stdout.readline())

    if result[0] == 'Error':
      print (result[1])
    elif result[0] == 'Ok':
      pass
    else:
      pass

  def get_env(self):
    json.dump(['GetEnv', get_client_state()], self.pipe.stdin)
    res = json.loads(self.pipe.stdout.readline())

    raise_if_error(res)
    if res[0] == 'SetInfoWindow':
      self.get_info_window().buffer[:] = res[1]
    else:
      pass

slick_process = None
def get_slick_process():
  global slick_process

  if not slick_process:
    slick_process = SlickProcess()
    slick_process.start()

  return slick_process

def get_env():
  get_slick_process().get_env()

def raise_if_error(res):
  if res[0] == 'Error':
    raise Exception(res[1])

