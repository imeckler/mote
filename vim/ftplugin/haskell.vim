" should be something like: call mote#register()
call mote#start()

" Possible key bindings:
" nnoremap <leader>n :call mote#nextHole()<cr>:call mote#getEnv()<cr>
" nnoremap <leader>p :call mote#prevHole()<cr>:call mote#getEnv()<cr>
" nnoremap <leader>e :call mote#getEnv()<cr>
" nnoremap <leader>l :MoteLoadCurrentFile<cr>
" autocmd BufWritePost *.hs MoteLoadCurrentFile
"
" or
"
" nnoremap <Esc>e :call mote#nextHole()<cr>:call mote#getEnv()<cr>
" nnoremap <Esc>n :call mote#prevHole()<cr>:call mote#getEnv()<cr>
" nnoremap <Esc>r :call mote#prevHole()<cr>:MoteRefine 
" nnoremap <Esc>l :MoteLoadCurrentFile <cr>

