{module, unfold0}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 19}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/unfold0.erl",6}]}.
    {func_info,{atom,unfold0},{atom,a},0}.
  {label,2}.
    {allocate_zero,3,0}.
    {make_fun2,{f,18},0,0,0}.
    {move,{x,0},{y,2}}.
    {make_fun2,{f,16},0,0,0}.
    {move,{x,0},{y,1}}.
    {make_fun2,{f,14},0,0,0}.
    {move,{x,0},{y,0}}.
    {make_fun2,{f,12},0,0,0}.
    {test_heap,8,1}.
    {put_list,{x,0},nil,{x,0}}.
    {put_list,{y,0},{x,0},{x,0}}.
    {put_list,{y,1},{x,0},{x,0}}.
    {put_list,{y,2},{x,0},{y,2}}.
    {make_fun2,{f,10},0,0,0}.
    {move,{y,2},{x,2}}.
    {move,{literal,{r,undefined,undefined,undefined,undefined,undefined}},
          {x,1}}.
    {line,[{location,"test/unfold0.erl",12}]}.
    {call_ext_last,3,{extfunc,lists,foldl,3},3}.


{function, b, 0, 4}.
  {label,3}.
    {line,[{location,"test/unfold0.erl",14}]}.
    {func_info,{atom,unfold0},{atom,b},0}.
  {label,4}.
    {move,{literal,{r,undefined,"DEUX","trois",undefined,"cinq"}},{x,0}}.
    return.


{function, module_info, 0, 6}.
  {label,5}.
    {line,[]}.
    {func_info,{atom,unfold0},{atom,module_info},0}.
  {label,6}.
    {move,{atom,unfold0},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 8}.
  {label,7}.
    {line,[]}.
    {func_info,{atom,unfold0},{atom,module_info},1}.
  {label,8}.
    {move,{x,0},{x,1}}.
    {move,{atom,unfold0},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.


{function, '-a/0-fun-4-', 2, 10}.
  {label,9}.
    {line,[{location,"test/unfold0.erl",12}]}.
    {func_info,{atom,unfold0},{atom,'-a/0-fun-4-'},2}.
  {label,10}.
    {allocate,0,2}.
    {move,{x,1},{x,2}}.
    {move,{x,0},{x,1}}.
    {move,{x,2},{x,0}}.
    {line,[{location,"test/unfold0.erl",12}]}.
    {call_fun,1}.
    {deallocate,0}.
    return.


{function, '-a/0-fun-3-', 1, 12}.
  {label,11}.
    {line,[{location,"test/unfold0.erl",10}]}.
    {func_info,{atom,unfold0},{atom,'-a/0-fun-3-'},1}.
  {label,12}.
    {move,{x,0},{x,1}}.
    {move,{literal,"DEUX"},{x,2}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/unfold0.erl",10}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-2-', 1, 14}.
  {label,13}.
    {line,[{location,"test/unfold0.erl",9}]}.
    {func_info,{atom,unfold0},{atom,'-a/0-fun-2-'},1}.
  {label,14}.
    {move,{x,0},{x,1}}.
    {move,{literal,"cinq"},{x,2}}.
    {move,{integer,6},{x,0}}.
    {line,[{location,"test/unfold0.erl",9}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-1-', 1, 16}.
  {label,15}.
    {line,[{location,"test/unfold0.erl",8}]}.
    {func_info,{atom,unfold0},{atom,'-a/0-fun-1-'},1}.
  {label,16}.
    {move,{x,0},{x,1}}.
    {move,{literal,"trois"},{x,2}}.
    {move,{integer,4},{x,0}}.
    {line,[{location,"test/unfold0.erl",8}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-0-', 1, 18}.
  {label,17}.
    {line,[{location,"test/unfold0.erl",7}]}.
    {func_info,{atom,unfold0},{atom,'-a/0-fun-0-'},1}.
  {label,18}.
    {move,{x,0},{x,1}}.
    {move,{literal,"deux"},{x,2}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/unfold0.erl",7}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.
