module top;

initial
   begin
      integer filea, fileb, fileab;
      filea = $fopen("allmsgs.txt");
      fileb = $fopen("somemsgs.txt");
      fileab = filea | fileb;
      $fdisplay(filea,  "This goes to A");
      $fdisplay(fileb,  "This goes to B");
      $fdisplay(fileab, "This goes to both");
      $fclose(filea);$fclose(fileb);$fclose(fileab);
   end
endmodule

