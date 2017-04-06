package tinyalu_pkg;

typedef enum {add_op, and_op, xor_op, mul_op,no_op} operation_t;

class alu_operation;
   rand logic[7:0] A,B;
   rand operation_t op;

   function new (
       logic[7:0] ia = 0,
       logic[7:0] ib = 0,
       operation_t iop = no_op );
      A  = ia;
      B  = ib;
      op = iop;
   endfunction

   function alu_operation clone();
      alu_operation c;
      c = new(A,B,op);
      return c;
   endfunction

   function bit comp (alu_operation t);
      return ((t.A == A) && (t.B == B) && (t.op = op));
   endfunction

   function string convert2string;
      string str;
      $sformat(str,"A: %2h  B:%2h   OP:%s", A,B,op);
      return str;
   endfunction

   function logic [2:0] op2bits;
      case (op)
         add_op : op2bits = 3'b001;
         and_op : op2bits = 3'b010;
         xor_op : op2bits = 3'b011;
         mul_op : op2bits = 3'b100;
         no_op  : op2bits = 3'b000;
      endcase // case(op)
   endfunction //op2bits()

endclass

class alu_result;

   logic [15:0] result;

   function new( logic[15:0] iresult = 0);
      result=iresult;
   endfunction

   function alu_result clone();
      alu_result c;
      c = new(result);
      return c;
   endfunction

   function bit comp (alu_result r);
     return (r.result == result);
   endfunction

   function string convert2string;
      string str;
      $sformat(str,"Result: %h",result);
      return str;
   endfunction

endclass

endpackage

