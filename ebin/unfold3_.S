{module, unfold3}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 19}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/unfold3.erl",6}]}.
    {func_info,{atom,unfold3},{atom,a},0}.
  {label,2}.
    {allocate_zero,4,0}.
    {make_fun2,{f,18},0,0,0}.
    {move,{x,0},{y,3}}.
    {make_fun2,{f,16},0,0,0}.
    {move,{x,0},{y,2}}.
    {make_fun2,{f,14},0,0,0}.
    {move,{x,0},{y,1}}.
    {make_fun2,{f,12},0,0,0}.
    {move,{x,0},{y,0}}.
    {make_fun2,{f,10},0,0,0}.
    {test_heap,8,1}.
    {put_list,{x,0},nil,{x,3}}.
    {put_list,{y,0},{x,3},{x,3}}.
    {put_list,{y,1},{x,3},{x,3}}.
    {put_list,{y,2},{x,3},{x,2}}.
    {move,{literal,{r,undefined,undefined,undefined,undefined,undefined}},
          {x,1}}.
    {move,{y,3},{x,0}}.
    {line,[{location,"test/unfold3.erl",15}]}.
    {call_ext_last,3,{extfunc,lists,foldl,3},4}.


{function, b, 0, 4}.
  {label,3}.
    {line,[{location,"test/unfold3.erl",22}]}.
    {func_info,{atom,unfold3},{atom,b},0}.
  {label,4}.
    {move,{literal,{r,undefined,"DEUX","trois",undefined,"cinq"}},{x,0}}.
    return.


{function, module_info, 0, 6}.
  {label,5}.
    {line,[]}.
    {func_info,{atom,unfold3},{atom,module_info},0}.
  {label,6}.
    {move,{atom,unfold3},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 8}.
  {label,7}.
    {line,[]}.
    {func_info,{atom,unfold3},{atom,module_info},1}.
  {label,8}.
    {move,{x,0},{x,1}}.
    {move,{atom,unfold3},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.


{function, '-a/0-fun-4-', 1, 10}.
  {label,9}.
    {line,[{location,"test/unfold3.erl",18}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-4-'},1}.
  {label,10}.
    {move,{x,0},{x,1}}.
    {move,{literal,"DEUX"},{x,2}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/unfold3.erl",18}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-3-', 1, 12}.
  {label,11}.
    {line,[{location,"test/unfold3.erl",20}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-3-'},1}.
  {label,12}.
    {move,{x,0},{x,1}}.
    {move,{literal,"cinq"},{x,2}}.
    {move,{integer,6},{x,0}}.
    {line,[{location,"test/unfold3.erl",20}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-2-', 1, 14}.
  {label,13}.
    {line,[{location,"test/unfold3.erl",19}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-2-'},1}.
  {label,14}.
    {move,{x,0},{x,1}}.
    {move,{literal,"trois"},{x,2}}.
    {move,{integer,4},{x,0}}.
    {line,[{location,"test/unfold3.erl",19}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-1-', 1, 16}.
  {label,15}.
    {line,[{location,"test/unfold3.erl",17}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-1-'},1}.
  {label,16}.
    {move,{x,0},{x,1}}.
    {move,{literal,"deux"},{x,2}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/unfold3.erl",17}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, '-a/0-fun-0-', 2, 18}.
  {label,17}.
    {line,[{location,"test/unfold3.erl",15}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-0-'},2}.
  {label,18}.
    {allocate,0,2}.
    {move,{x,1},{x,2}}.
    {move,{x,0},{x,1}}.
    {move,{x,2},{x,0}}.
    {line,[{location,"test/unfold3.erl",15}]}.
    {call_fun,1}.
    {deallocate,0}.
    return.
