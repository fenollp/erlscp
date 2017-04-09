{module, deforestation10}.  %% version = 0

{exports, [{a,0},{a,1},{b,0},{b,1},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 22}.


{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"test/deforestation10.erl",4}]}.
    {func_info,{atom,deforestation10},{atom,a},0}.
  {label,2}.
    {allocate,0,0}.
    {move,{literal,[1,2]},{x,1}}.
    {move,{integer,3},{x,0}}.
    {line,[{location,"test/deforestation10.erl",6}]}.
    {call_ext,2,{extfunc,lists,member,2}}.
    {test,is_atom,{f,5},[{x,0}]}.
    {select_val,{x,0},{f,5},{list,[{atom,true},{f,3},{atom,false},{f,4}]}}.
  {label,3}.
    {move,{literal,[blip,blop,3]},{x,0}}.
    {line,[{location,"test/deforestation10.erl",8}]}.
    {call_ext_last,1,{extfunc,do,the_thing,1},0}.
  {label,4}.
    {move,{literal,"usage: ...\n"},{x,1}}.
    {move,nil,{x,2}}.
    {move,{atom,standard_error},{x,0}}.
    {line,[{location,"test/deforestation10.erl",7}]}.
    {call_ext_last,3,{extfunc,io,format,3},0}.
  {label,5}.
    {move,{atom,badarg},{x,0}}.
    {line,[{location,"test/deforestation10.erl",6}]}.
    {call_ext_last,1,{extfunc,erlang,error,1},0}.


{function, a, 1, 7}.
  {label,6}.
    {line,[{location,"test/deforestation10.erl",5}]}.
    {func_info,{atom,deforestation10},{atom,a},1}.
  {label,7}.
    {allocate_zero,1,1}.
    {line,[{location,"test/deforestation10.erl",6}]}.
    {gc_bif,length,{f,0},1,[{x,0}],{x,1}}.
    {move,{x,0},{y,0}}.
    {move,{x,1},{x,0}}.
    {move,{literal,[1,2]},{x,1}}.
    {line,[{location,"test/deforestation10.erl",6}]}.
    {call_ext,2,{extfunc,lists,member,2}}.
    {test,is_atom,{f,10},[{x,0}]}.
    {select_val,{x,0},{f,10},{list,[{atom,true},{f,8},{atom,false},{f,9}]}}.
  {label,8}.
    {move,{y,0},{x,0}}.
    {line,[{location,"test/deforestation10.erl",8}]}.
    {call_ext_last,1,{extfunc,do,the_thing,1},1}.
  {label,9}.
    {move,{literal,"usage: ...\n"},{x,1}}.
    {move,nil,{x,2}}.
    {move,{atom,standard_error},{x,0}}.
    {line,[{location,"test/deforestation10.erl",7}]}.
    {call_ext_last,3,{extfunc,io,format,3},1}.
  {label,10}.
    {move,{atom,badarg},{x,0}}.
    {line,[{location,"test/deforestation10.erl",6}]}.
    {call_ext_last,1,{extfunc,erlang,error,1},1}.


{function, b, 0, 12}.
  {label,11}.
    {line,[{location,"test/deforestation10.erl",11}]}.
    {func_info,{atom,deforestation10},{atom,b},0}.
  {label,12}.
    {move,{literal,[bla]},{x,0}}.
    {test,is_nonempty_list,{f,13},[{x,0}]}.
    {get_list,{x,0},{x,1},{x,2}}.
    {test,is_nil,{f,13},[{x,2}]}.
    {move,{literal,"usage: ...\n"},{x,1}}.
    {move,nil,{x,2}}.
    {move,{atom,standard_error},{x,0}}.
    {line,[{location,"test/deforestation10.erl",12}]}.
    {call_ext_only,3,{extfunc,io,format,3}}.
  {label,13}.
    if_end.


{function, b, 1, 15}.
  {label,14}.
    {line,[{location,"test/deforestation10.erl",12}]}.
    {func_info,{atom,deforestation10},{atom,b},1}.
  {label,15}.
    {test,is_nonempty_list,{f,14},[{x,0}]}.
    {get_list,{x,0},{x,1},{x,2}}.
    {test,is_nonempty_list,{f,16},[{x,2}]}.
    {get_list,{x,2},{x,1},{x,3}}.
    {test,is_nil,{f,17},[{x,3}]}.
    {move,{literal,"usage: ...\n"},{x,1}}.
    {move,nil,{x,2}}.
    {move,{atom,standard_error},{x,0}}.
    {line,[{location,"test/deforestation10.erl",13}]}.
    {call_ext_only,3,{extfunc,io,format,3}}.
  {label,16}.
    {test,is_nil,{f,17},[{x,2}]}.
    {move,{literal,"usage: ...\n"},{x,1}}.
    {move,nil,{x,2}}.
    {move,{atom,standard_error},{x,0}}.
    {line,[{location,"test/deforestation10.erl",12}]}.
    {call_ext_only,3,{extfunc,io,format,3}}.
  {label,17}.
    {line,[{location,"test/deforestation10.erl",14}]}.
    {call_ext_only,1,{extfunc,do,the_thing,1}}.


{function, module_info, 0, 19}.
  {label,18}.
    {line,[]}.
    {func_info,{atom,deforestation10},{atom,module_info},0}.
  {label,19}.
    {move,{atom,deforestation10},{x,0}}.
    {line,[]}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 21}.
  {label,20}.
    {line,[]}.
    {func_info,{atom,deforestation10},{atom,module_info},1}.
  {label,21}.
    {move,{x,0},{x,1}}.
    {move,{atom,deforestation10},{x,0}}.
    {line,[]}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
