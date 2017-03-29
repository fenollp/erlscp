{module, unfold3}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 29}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/unfold3.erl",6}]}.
    {func_info,{atom,unfold3},{atom,a},0}.
  {label,2}.
    {allocate_zero,1,0}.
    {make_fun2,{f,28},0,0,0}.
    {test_heap,2,1}.
    {put_list,{x,0},nil,{y,0}}.
    {make_fun2,{f,26},0,0,0}.
    {test_heap,2,1}.
    {put_list,{x,0},{y,0},{y,0}}.
    {make_fun2,{f,24},0,0,0}.
    {test_heap,2,1}.
    {put_list,{x,0},{y,0},{y,0}}.
    {make_fun2,{f,22},0,0,0}.
    {test_heap,2,1}.
    {put_list,{x,0},{y,0},{x,1}}.
    {move,{literal,{r,undefined,undefined,undefined,undefined,undefined}},
          {x,0}}.
    {call_last,2,{f,4},1}.


{function, pipe, 2, 4}.
  {label,3}.
    {line,[{location,"test/unfold3.erl",14}]}.
    {func_info,{atom,unfold3},{atom,pipe},2}.
  {label,4}.
    {allocate,2,2}.
    {move,{x,1},{y,0}}.
    {move,{x,0},{y,1}}.
    {make_fun2,{f,20},0,0,0}.
    {move,{y,0},{x,2}}.
    {move,{y,1},{x,1}}.
    {line,[{location,"test/unfold3.erl",15}]}.
    {call_ext_last,3,{extfunc,lists,foldl,3},2}.


{function, two, 1, 6}.
  {label,5}.
    {line,[{location,"test/unfold3.erl",17}]}.
    {func_info,{atom,unfold3},{atom,two},1}.
  {label,6}.
    {move,{x,0},{x,1}}.
    {move,{literal,"deux"},{x,2}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/unfold3.erl",17}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, 'TWO', 1, 8}.
  {label,7}.
    {line,[{location,"test/unfold3.erl",18}]}.
    {func_info,{atom,unfold3},{atom,'TWO'},1}.
  {label,8}.
    {move,{x,0},{x,1}}.
    {move,{literal,"DEUX"},{x,2}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/unfold3.erl",18}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, three, 1, 10}.
  {label,9}.
    {line,[{location,"test/unfold3.erl",19}]}.
    {func_info,{atom,unfold3},{atom,three},1}.
  {label,10}.
    {move,{x,0},{x,1}}.
    {move,{literal,"trois"},{x,2}}.
    {move,{integer,4},{x,0}}.
    {line,[{location,"test/unfold3.erl",19}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, five, 1, 12}.
  {label,11}.
    {line,[{location,"test/unfold3.erl",20}]}.
    {func_info,{atom,unfold3},{atom,five},1}.
  {label,12}.
    {move,{x,0},{x,1}}.
    {move,{literal,"cinq"},{x,2}}.
    {move,{integer,6},{x,0}}.
    {line,[{location,"test/unfold3.erl",20}]}.
    {call_ext_only,3,{extfunc,erlang,setelement,3}}.


{function, b, 0, 14}.
  {label,13}.
    {line,[{location,"test/unfold3.erl",22}]}.
    {func_info,{atom,unfold3},{atom,b},0}.
  {label,14}.
    {move,{literal,{r,undefined,"DEUX","trois",undefined,"cinq"}},{x,0}}.
    return.


{function, module_info, 0, 16}.
  {label,15}.
    {line,[]}.
    {func_info,{atom,unfold3},{atom,module_info},0}.
  {label,16}.
    {move,{atom,unfold3},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 18}.
  {label,17}.
    {line,[]}.
    {func_info,{atom,unfold3},{atom,module_info},1}.
  {label,18}.
    {move,{x,0},{x,1}}.
    {move,{atom,unfold3},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.


{function, '-pipe/2-fun-0-', 2, 20}.
  {label,19}.
    {line,[{location,"test/unfold3.erl",15}]}.
    {func_info,{atom,unfold3},{atom,'-pipe/2-fun-0-'},2}.
  {label,20}.
    {allocate,0,2}.
    {move,{x,1},{x,2}}.
    {move,{x,0},{x,1}}.
    {move,{x,2},{x,0}}.
    {line,[{location,"test/unfold3.erl",15}]}.
    {call_fun,1}.
    {deallocate,0}.
    return.


{function, '-a/0-fun-0-', 1, 22}.
  {label,21}.
    {line,[{location,"test/unfold3.erl",7}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-0-'},1}.
  {label,22}.
    {call_only,1,{f,6}}.


{function, '-a/0-fun-1-', 1, 24}.
  {label,23}.
    {line,[{location,"test/unfold3.erl",8}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-1-'},1}.
  {label,24}.
    {call_only,1,{f,10}}.


{function, '-a/0-fun-2-', 1, 26}.
  {label,25}.
    {line,[{location,"test/unfold3.erl",9}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-2-'},1}.
  {label,26}.
    {call_only,1,{f,12}}.


{function, '-a/0-fun-3-', 1, 28}.
  {label,27}.
    {line,[{location,"test/unfold3.erl",10}]}.
    {func_info,{atom,unfold3},{atom,'-a/0-fun-3-'},1}.
  {label,28}.
    {call_only,1,{f,8}}.
