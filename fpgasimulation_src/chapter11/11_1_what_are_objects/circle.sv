class circle;

  real radius;

  function new(real r);
     radius = r;
  endfunction

  function real diameter;
    return radius * 2;
  endfunction

  function real area;
    return 3.14159 * radius**2;
  endfunction

  function real circumference;
    return 2 * 3.14159 * radius;
  endfunction

endclass



module circle_mod;

   circle c;

   initial begin
       c = new (2.5);
       $display("Radius\t%4.2f", c.radius);
       $display("Diameter\t%4.2f",c.diameter);
       $display("Area\t\t%4.2f",c.area);
       $display("Circumference\t%4.2f",c.circumference);
   end

endmodule

