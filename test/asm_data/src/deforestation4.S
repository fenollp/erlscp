{deforestation4,
    [{a,0},{b,0},{module_info,0},{module_info,1}],
    [],
    [{function,a,0,2,
         [{label,1},
          {line,[{location,"test/asm_data/deforestation4.erl",6}]},
          {func_info,{atom,deforestation4},{atom,a},0},
          {label,2},
          {move,{literal,["app [","my_app",<<"]">>]},{x,0}},
          {line,[{location,"test/asm_data/deforestation4.erl",6}]},
          {call_ext_only,1,{extfunc,erlang,iolist_to_binary,1}}]},
     {function,b,0,4,
         [{label,3},
          {line,[{location,"test/asm_data/deforestation4.erl",8}]},
          {func_info,{atom,deforestation4},{atom,b},0},
          {label,4},
          {move,{literal,<<"app [my_app]">>},{x,0}},
          return]},
     {function,module_info,0,6,
         [{label,5},
          {line,[]},
          {func_info,{atom,deforestation4},{atom,module_info},0},
          {label,6},
          {move,{atom,deforestation4},{x,0}},
          {line,[]},
          {call_ext_only,1,{extfunc,erlang,get_module_info,1}}]},
     {function,module_info,1,8,
         [{label,7},
          {line,[]},
          {func_info,{atom,deforestation4},{atom,module_info},1},
          {label,8},
          {move,{x,0},{x,1}},
          {move,{atom,deforestation4},{x,0}},
          {line,[]},
          {call_ext_only,2,{extfunc,erlang,get_module_info,2}}]}],
    9}
