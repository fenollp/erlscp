{module, map4}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 13}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/map4.erl",4}]}.
    {func_info,{atom,map4},{atom,a},0}.
  {label,2}.
    {allocate_zero,1,0}.
    {move,{literal,#{key => b}},{x,0}}.
    {get_map_elements,{f,4},{x,0},{list,[{atom,key},{x,1}]}}.
    {move,{x,1},{y,0}}.
    {make_fun2,{f,12},0,0,0}.
    {move,{x,0},{x,1}}.
    {move,{y,0},{x,0}}.
    {line,[{location,"test/map4.erl",6}]}.
    {call_fun,1}.
    {test,is_map,{f,3},[{x,0}]}.
    {line,[{location,"test/map4.erl",7}]}.
    {put_map_assoc,{f,0},{x,0},{x,0},1,{list,[{atom,a},{integer,42}]}}.
    {line,[{location,"test/map4.erl",7}]}.
    {put_map_assoc,{f,0},{x,0},{x,0},1,{list,[{y,0},{integer,1}]}}.
    {deallocate,1}.
    return.
  {label,3}.
    {test_heap,3,1}.
    {put_tuple,2,{x,1}}.
    {put,{atom,badmap}}.
    {put,{x,0}}.
    {move,{x,1},{x,0}}.
    {line,[{location,"test/map4.erl",7}]}.
    {call_ext,1,{extfunc,erlang,error,1}}.
  {label,4}.
    {line,[{location,"test/map4.erl",5}]}.
    {badmatch,{x,0}}.


{function, b, 0, 6}.
  {label,5}.
    {line,[{location,"test/map4.erl",9}]}.
    {func_info,{atom,map4},{atom,b},0}.
  {label,6}.
    {move,{literal,#{a => 42,b => 1}},{x,0}}.
    return.


{function, module_info, 0, 8}.
  {label,7}.
    {line,[]}.
    {func_info,{atom,map4},{atom,module_info},0}.
  {label,8}.
    {move,{atom,map4},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 10}.
  {label,9}.
    {line,[]}.
    {func_info,{atom,map4},{atom,module_info},1}.
  {label,10}.
    {move,{x,0},{x,1}}.
    {move,{atom,map4},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.


{function, '-a/0-fun-0-', 1, 12}.
  {label,11}.
    {line,[{location,"test/map4.erl",6}]}.
    {func_info,{atom,map4},{atom,'-a/0-fun-0-'},1}.
  {label,12}.
    {line,[{location,"test/map4.erl",6}]}.
    {put_map_assoc,{f,0},{literal,#{}},{x,0},1,{list,[{atom,a},{x,0}]}}.
    return.
