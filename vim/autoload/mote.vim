function! mote#CreateInfoWindow()
  let l:currwin = winnr()
  rightbelow 10new HoleInfo
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
py import mote

function! mote#start()
  sign define hole text=@ texthl=Search
  py mote.start()
endfunction

function! mote#stop()
  py mote.stop()
endfunction

function! mote#loadCurrentFile()
  py mote.load_current_file()
  sign unplace 666
endfunction

function! mote#getEnv()
  " py cw = vim.current.window
  " py c  = cw.cursor
  sign unplace 666
  exe "sign place 666 line=" . line(".") . " name=hole file=" . expand("%:p")
  py mote.enter_hole()
  py mote.get_env()
  redraw!
  " py cw.cursor = c
  " py vim.current.window = cw
  " call setpos('.', getpos('.'))  hack to get it to draw right
endfunction

function! mote#getType(e)
  py mote.get_type(vim.eval('a:e'))
endfunction

function! mote#refine(e)
  py mote.refine(vim.eval('a:e'))
  redraw!
  write
  call mote#loadCurrentFile()
endfunction

function! mote#nextHole()
  py mote.next_hole()
  redraw!
endfunction

function! mote#prevHole()
  py mote.prev_hole()
  redraw!
endfunction

function! mote#nextHoleAndGetEnv()
  call mote#nextHole()
  call mote#getEnv()
endfunction

function! mote#prevHoleAndGetEnv()
  call mote#prevHole()
  call mote#getEnv()
endfunction

function! mote#caseFurther(x)
  py mote.case_further(vim.eval('a:x'))
  redraw!
  write
  call mote#loadCurrentFile()
endfunction

function! mote#caseOn(e)
  py mote.case_on(vim.eval('a:e'))
  redraw!
  write
  call mote#loadCurrentFile()
endfunction

augroup moteGroup
  autocmd VimLeave * :call mote#stop()
  autocmd BufWritePost *.hs MoteLoadCurrentFile
augroup END

let g:mote_mode = 1
function! mote#toggleMode()
  if g:mote_mode == 1
    autocmd! moteGroup BufWritePost 
    let g:mote_mode = 0
  else
    augroup moteGroup
      autocmd BufWritePost *.hs MoteLoadCurrentFile
    augroup END
    let g:mote_mode = 1 - g:mote_mode
  endif
endfunction

command! MoteStart  call mote#start()
command! MoteLoadCurrentFile call mote#loadCurrentFile()
command! MoteGetEnv call mote#getEnv()
command! MoteNextHole call mote#nextHoleAndGetEnv()
command! MotePrevHole call mote#prevHoleAndGetEnv()
command! -nargs=1 MoteGetType call mote#getType(<f-args>)
command! -nargs=1 MoteRefine call mote#refine(<f-args>)
command! -nargs=1 Casex call mote#caseFurther(<f-args>)
command! -nargs=1 CaseOn call mote#caseOn(<f-args>)
command! MoteToggleMode call mote#toggleMode()

