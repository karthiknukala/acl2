interface simplebus ;

  logic [2:0] bar;
  logic [3:0] baz;

  modport master (input bar, output .whoo(baaz)); // oops, baaz not declared

endinterface

module top (output topout, input topin);

  wire foo;

  simplebus sb (foo);

endmodule
