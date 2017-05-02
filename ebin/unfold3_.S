{module, unfold3}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 9}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/unfold3.erl",6}]}.
    {func_info,{atom,unfold3},{atom,a},0}.
  {label,2}.
    {move,{literal,{r,undefined,"DEUX","trois",undefined,"cinq"}},{x,0}}.
    return.


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
