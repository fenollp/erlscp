{module, map3}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 9}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/map3.erl",4}]}.
    {func_info,{atom,map3},{atom,a},0}.
  {label,2}.
    {move,{literal,#{a => 42,b => 1}},{x,0}}.
    return.


{function, b, 0, 4}.
  {label,3}.
    {line,[{location,"test/map3.erl",9}]}.
    {func_info,{atom,map3},{atom,b},0}.
  {label,4}.
    {move,{literal,#{a => 42,b => 1}},{x,0}}.
    return.


{function, module_info, 0, 6}.
  {label,5}.
    {line,[]}.
    {func_info,{atom,map3},{atom,module_info},0}.
  {label,6}.
    {move,{atom,map3},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 8}.
  {label,7}.
    {line,[]}.
    {func_info,{atom,map3},{atom,module_info},1}.
  {label,8}.
    {move,{x,0},{x,1}}.
    {move,{atom,map3},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
