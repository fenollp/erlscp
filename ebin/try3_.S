{module, try3}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 10}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/try3.erl",4}]}.
    {func_info,{atom,try3},{atom,a},0}.
  {label,2}.
    {allocate,1,0}.
    {'catch',{y,0},{f,3}}.
    {line,[{location,"test/try3.erl",5}]}.
    {call_ext,0,{extfunc,erlang,get,0}}.
  {label,3}.
    {catch_end,{y,0}}.
    {deallocate,1}.
    return.


{function, b, 0, 5}.
  {label,4}.
    {line,[{location,"test/try3.erl",7}]}.
    {func_info,{atom,try3},{atom,b},0}.
  {label,5}.
    {call_ext_only,0,{extfunc,erlang,get,0}}.


{function, module_info, 0, 7}.
  {label,6}.
    {line,[]}.
    {func_info,{atom,try3},{atom,module_info},0}.
  {label,7}.
    {move,{atom,try3},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 9}.
  {label,8}.
    {line,[]}.
    {func_info,{atom,try3},{atom,module_info},1}.
  {label,9}.
    {move,{x,0},{x,1}}.
    {move,{atom,try3},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
