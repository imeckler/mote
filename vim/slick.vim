py import slick

function! slick#CreateInfoWindow()
  let l:currwin = winnr()
  rightbelow new HoleInfo
    let l:infowin = winnr()
    setlocal buftype=nofile
    setlocal noswapfile
  execute l:currwin . 'winc w'

  return l:infowin
endfunction

