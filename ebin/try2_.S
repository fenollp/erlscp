{module, try2}.  %% version = 0

{exports, [{a,0},{b,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 14}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/try2.erl",4}]}.
    {func_info,{atom,try2},{atom,a},0}.
  {label,2}.
    {allocate,1,0}.
    {'try',{y,0},{f,6}}.
    {line,[{location,"test/try2.erl",5}]}.
    {call_ext,0,{extfunc,erlang,get,0}}.
    {try_end,{y,0}}.
    {test,bs_start_match2,{f,5},1,[{x,0},0],{x,1}}.
    {test,bs_get_integer2,
          {f,4},
          2,
          [{x,1},
           {integer,8},
           1,
           {field_flags,[{anno,[6,{file,"test/try2.erl"}]},unsigned,big]}],
          {x,2}}.
    {test,is_eq_exact,{f,3},[{x,2},{integer,97}]}.
    {test,bs_match_string,{f,3},[{x,1},16,{string,"bc"}]}.
    {test,bs_test_tail2,{f,3},[{x,1},0]}.
    {move,{literal,<<"def">>},{x,0}}.
    {deallocate,1}.
    return.
  {label,3}.
    {bs_restore2,{x,1},{atom,start}}.
  {label,4}.
    {test,bs_get_utf8,
          {f,5},
          2,
          [{x,1},
           {field_flags,[{anno,[7,{file,"test/try2.erl"}]},unsigned,big]}],
          {x,2}}.
    {test,is_eq_exact,{f,5},[{x,2},{integer,960}]}.
    {test,bs_test_tail2,{f,5},[{x,1},0]}.
    {move,{float,3.14},{x,0}}.
    {deallocate,1}.
    return.
  {label,5}.
    {test,is_list,{f,7},[{x,0}]}.
    {deallocate,1}.
    return.
  {label,6}.
    {try_case,{y,0}}.
    {move,{atom,impossible},{x,0}}.
    {deallocate,1}.
    return.
  {label,7}.
    {line,[{location,"test/try2.erl",5}]}.
    {try_case_end,{x,0}}.


{function, b, 0, 9}.
  {label,8}.
    {line,[{location,"test/try2.erl",13}]}.
    {func_info,{atom,try2},{atom,b},0}.
  {label,9}.
    {call_ext_only,0,{extfunc,erlang,get,0}}.


{function, module_info, 0, 11}.
  {label,10}.
    {line,[]}.
    {func_info,{atom,try2},{atom,module_info},0}.
  {label,11}.
    {move,{atom,try2},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 13}.
  {label,12}.
    {line,[]}.
    {func_info,{atom,try2},{atom,module_info},1}.
  {label,13}.
    {move,{x,0},{x,1}}.
    {move,{atom,try2},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
