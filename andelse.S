{module, andelse}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 9}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"andelse.erl",4}]}.
    {func_info,{atom,andelse},{atom,a},0}.
  {label,2}.
    {line,[{location,"andelse.erl",7}]}.
    {call_ext_only,0,{extfunc,my,call,0}}.


{function, b, 0, 4}.
  {label,3}.
    {line,[{location,"andelse.erl",10}]}.
    {func_info,{atom,andelse},{atom,b},0}.
  {label,4}.
    {line,[{location,"andelse.erl",11}]}.
    {call_ext_only,0,{extfunc,my,call,0}}.


{function, module_info, 0, 6}.
  {label,5}.
    {line,[]}.
    {func_info,{atom,andelse},{atom,module_info},0}.
  {label,6}.
    {move,{atom,andelse},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 8}.
  {label,7}.
    {line,[]}.
    {func_info,{atom,andelse},{atom,module_info},1}.
  {label,8}.
    {move,{x,0},{x,1}}.
    {move,{atom,andelse},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
