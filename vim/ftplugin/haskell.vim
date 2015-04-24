" should be something like: call slick#register()
call slick#start()

" Possible key bindings:
" nnoremap <leader>n :call slick#nextHole()<cr>:call slick#getEnv()<cr>
" nnoremap <leader>p :call slick#prevHole()<cr>:call slick#getEnv()<cr>
" nnoremap <leader>e :call slick#getEnv()<cr>
" nnoremap <leader>l :call slick#loadCurrentFile()<cr>
" autocmd BufWritePost *.hs SlickLoadCurrentFile
"
" or
"
" nnoremap <Esc>e :call slick#nextHole()<cr>:call slick#getEnv()<cr>
" nnoremap <Esc>n :call slick#prevHole()<cr>:call slick#getEnv()<cr>
" nnoremap <Esc>r :call slick#prevHole()<cr>:SlickRefine 
" nnoremap <Esc>l :SlickLoadCurrentFile <cr>
" autocmd BufWritePost *.hs SlickLoadCurrentFile

