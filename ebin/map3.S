{module, map3}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 12}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/map3.erl",4}]}.
    {func_info,{atom,map3},{atom,a},0}.
  {label,2}.
    {allocate,0,0}.
    {make_fun2,{f,11},0,0,0}.
    {move,{x,0},{x,1}}.
    {move,{atom,b},{x,0}}.
    {line,[{location,"test/map3.erl",6}]}.
    {call_fun,1}.
    {test,is_map,{f,3},[{x,0}]}.
    {line,[{location,"test/map3.erl",7}]}.
    {put_map_assoc,{f,0},
                   {x,0},
                   {x,0},
                   1,
                   {list,[{atom,a},{integer,42},{atom,b},{integer,1}]}}.
    {deallocate,0}.
    return.
  {label,3}.
    {test_heap,3,1}.
    {put_tuple,2,{x,1}}.
    {put,{atom,badmap}}.
    {put,{x,0}}.
    {move,{x,1},{x,0}}.
    {line,[{location,"test/map3.erl",7}]}.
    {call_ext,1,{extfunc,erlang,error,1}}.


{function, b, 0, 5}.
  {label,4}.
    {line,[{location,"test/map3.erl",9}]}.
    {func_info,{atom,map3},{atom,b},0}.
  {label,5}.
    {move,{literal,#{a => 42,b => 1}},{x,0}}.
    return.


{function, module_info, 0, 7}.
  {label,6}.
    {line,[]}.
    {func_info,{atom,map3},{atom,module_info},0}.
  {label,7}.
    {move,{atom,map3},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 9}.
  {label,8}.
    {line,[]}.
    {func_info,{atom,map3},{atom,module_info},1}.
  {label,9}.
    {move,{x,0},{x,1}}.
    {move,{atom,map3},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.


{function, '-a/0-fun-0-', 1, 11}.
  {label,10}.
    {line,[{location,"test/map3.erl",6}]}.
    {func_info,{atom,map3},{atom,'-a/0-fun-0-'},1}.
  {label,11}.
    {line,[{location,"test/map3.erl",6}]}.
    {put_map_assoc,{f,0},{literal,#{}},{x,0},1,{list,[{atom,a},{x,0}]}}.
    return.
