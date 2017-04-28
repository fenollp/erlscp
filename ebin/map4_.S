{module, map4}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 11}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/map4.erl",4}]}.
    {func_info,{atom,map4},{atom,a},0}.
  {label,2}.
    {move,{literal,#{key => b}},{x,0}}.
    {get_map_elements,{f,4},{x,0},{list,[{atom,key},{x,1}]}}.
    {line,[{location,"test/map4.erl",6}]}.
    {put_map_assoc,{f,0},{literal,#{}},{x,0},2,{list,[{atom,a},{x,1}]}}.
    {test,is_map,{f,3},[{x,0}]}.
    {line,[{location,"test/map4.erl",7}]}.
    {put_map_assoc,{f,0},{x,0},{x,0},2,{list,[{atom,a},{integer,42}]}}.
    {line,[{location,"test/map4.erl",7}]}.
    {put_map_assoc,{f,0},{x,0},{x,0},2,{list,[{x,1},{integer,1}]}}.
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
    {line,[{location,"test/map4.erl",4}]}.
    {case_end,{x,0}}.


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
