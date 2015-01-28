function! slick#CreateInfoWindow()
  let l:currwin = winnr()
  rightbelow 50vnew HoleInfo
    let l:infowin = winnr()
    setlocal buftype=nofile
    setlocal noswapfile
  execute l:currwin . 'winc w'

  return l:infowin
endfunction

let s:current_dir=expand("<sfile>:p:h")
py import sys, vim
py if not vim.eval("s:current_dir") in sys.path:
\ sys.path.append(vim.eval("s:current_dir"))
py import slick

function! slick#start()
  py slick.start()
endfunction

function! slick#stop()
  py slick.stop()
endfunction

function! slick#loadCurrentFile()
  py slick.load_current_file()
endfunction

function! slick#getEnv()
  py cw = vim.current.window
  py c  = cw.cursor
  py slick.enter_hole()
  py slick.get_env()
  redraw!
  " py cw.cursor = c
  " py vim.current.window = cw
  " call setpos('.', getpos('.'))  hack to get it to draw right
endfunction

function! slick#getType(e)
  py slick.get_type(vim.eval('a:e'))
endfunction

function! slick#nextHole()
  py slick.next_hole()
  redraw!
endfunction

function! slick#prevHole()
  py slick.prev_hole()
  redraw!
endfunction

augroup slickGroup
  autocmd VimLeave * :call slick#stop()
augroup END

command! SlickStart   call slick#start()
command! SlickGetType -nargs=1 call slick#getType(<args>)
command! SlickLoadCurrentFIle call slick#loadCurrentFile()
command! SlickGetEnv call slick#getEnv()

