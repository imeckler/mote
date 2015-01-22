function! slick#CreateInfoWindow()
  let l:currwin = winnr()
  rightbelow new HoleInfo
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
  py slick#stop()
endfunction

function! slick#loadCurrentFile()
  py slick.load_current_file()
endfunction

function! slick#getEnv()
  py slick.enter_hole()
  py slick.get_env()
  redraw
endfunction

function! slick#stuff()
  py slick.start()
  py slick.load_current_file()
  call cursor(8, 23)
  py slick
  py slick.enter_hole()
  py slick.get_env()
endfunction
