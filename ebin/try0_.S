{module, try0}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 14}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/try0.erl",4}]}.
    {func_info,{atom,try0},{atom,a},0}.
  {label,2}.
    {allocate,0,0}.
    {bif,self,{f,0},[],{x,0}}.
    {move,{integer,42},{x,1}}.
    {line,[{location,"test/try0.erl",5}]}.
    send.
    {test,is_eq_exact,{f,7},[{x,0},{integer,42}]}.
    {line,[{location,"test/try0.erl",6}]}.
  {label,3}.
    {loop_rec,{f,6},{x,0}}.
    {test,bs_start_match2,{f,4},1,[{x,0},0],{x,1}}.
    {test,bs_match_string,{f,5},[{x,1},32,{string,"this"}]}.
    {test,bs_test_tail2,{f,5},[{x,1},0]}.
    remove_message.
    {move,{atom,that},{x,0}}.
    {deallocate,0}.
    return.
  {label,4}.
    {test,is_eq_exact,{f,5},[{x,0},{integer,42}]}.
    remove_message.
    {move,{integer,5},{x,1}}.
    {move,{integer,1},{x,0}}.
    {line,[{location,"test/try0.erl",8}]}.
    {call_ext,2,{extfunc,lists,seq,2}}.
    {line,[{location,"test/try0.erl",8}]}.
    {gc_bif,length,{f,0},1,[{x,0}],{x,0}}.
    {deallocate,0}.
    return.
  {label,5}.
    {loop_rec_end,{f,3}}.
  {label,6}.
    timeout.
    {move,{atom,argh},{x,0}}.
    {line,[{location,"test/try0.erl",10}]}.
    {call_ext,1,{extfunc,erlang,throw,1}}.
  {label,7}.
    {line,[{location,"test/try0.erl",4}]}.
    {case_end,{x,0}}.


{function, b, 0, 9}.
  {label,8}.
    {line,[{location,"test/try0.erl",13}]}.
    {func_info,{atom,try0},{atom,b},0}.
  {label,9}.
    {move,{integer,5},{x,0}}.
    return.


{function, module_info, 0, 11}.
  {label,10}.
    {line,[]}.
    {func_info,{atom,try0},{atom,module_info},0}.
  {label,11}.
    {move,{atom,try0},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 13}.
  {label,12}.
    {line,[]}.
    {func_info,{atom,try0},{atom,module_info},1}.
  {label,13}.
    {move,{x,0},{x,1}}.
    {move,{atom,try0},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
