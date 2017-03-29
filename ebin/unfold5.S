{module, unfold5}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 17}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/unfold5.erl",6}]}.
    {func_info,{atom,unfold5},{atom,a},0}.
  {label,2}.
    {allocate,0,0}.
    {make_fun2,{f,16},0,0,0}.
    {line,[{location,"test/unfold5.erl",8}]}.
    {call_fun,0}.
    {make_fun2,{f,14},0,0,1}.
    {line,[{location,"test/unfold5.erl",9}]}.
    {call_fun,0}.
    {make_fun2,{f,12},0,0,1}.
    {line,[{location,"test/unfold5.erl",10}]}.
    {call_fun,0}.
    {make_fun2,{f,10},0,0,1}.
    {line,[{location,"test/unfold5.erl",11}]}.
    {call_fun,0}.
    {deallocate,0}.
    return.


{function, b, 0, 4}.
  {label,3}.
    {line,[{location,"test/unfold5.erl",14}]}.
    {func_info,{atom,unfold5},{atom,b},0}.
  {label,4}.
    {move,{literal,{r,undefined,"DEUX","trois",undefined,"cinq"}},{x,0}}.
    return.


{function, module_info, 0, 6}.
  {label,5}.
    {line,[]}.
    {func_info,{atom,unfold5},{atom,module_info},0}.
  {label,6}.
    {move,{atom,unfold5},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 8}.
  {label,7}.
    {line,[]}.
    {func_info,{atom,unfold5},{atom,module_info},1}.
  {label,8}.
    {move,{x,0},{x,1}}.
    {move,{atom,unfold5},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.


{function, '-a/0-fun-3-', 1, 10}.
  {label,9}.
    {line,[{location,"test/unfold5.erl",11}]}.
    {func_info,{atom,unfold5},{atom,'-a/0-fun-3-'},1}.
  {label,10}.
    {move,{x,0},{x,1}}.
    {move,{literal,"DEUX"},{x,2}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/unfold5.erl",11}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-2-', 1, 12}.
  {label,11}.
    {line,[{location,"test/unfold5.erl",10}]}.
    {func_info,{atom,unfold5},{atom,'-a/0-fun-2-'},1}.
  {label,12}.
    {move,{x,0},{x,1}}.
    {move,{literal,"cinq"},{x,2}}.
    {move,{integer,6},{x,0}}.
    {line,[{location,"test/unfold5.erl",10}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-1-', 1, 14}.
  {label,13}.
    {line,[{location,"test/unfold5.erl",9}]}.
    {func_info,{atom,unfold5},{atom,'-a/0-fun-1-'},1}.
  {label,14}.
    {move,{x,0},{x,1}}.
    {move,{literal,"trois"},{x,2}}.
    {move,{integer,4},{x,0}}.
    {line,[{location,"test/unfold5.erl",9}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-0-', 0, 16}.
  {label,15}.
    {line,[{location,"test/unfold5.erl",8}]}.
    {func_info,{atom,unfold5},{atom,'-a/0-fun-0-'},0}.
  {label,16}.
    {move,{literal,{r,undefined,"deux",undefined,undefined,undefined}},{x,0}}.
    return.
