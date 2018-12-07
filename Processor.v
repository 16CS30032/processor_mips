// S. SASI BHUSHAN 16CS30032
//K. SAI SURYA TEJA 16CS30015
//GRP - 46
`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    14:32:18 10/08/2018 
// Design Name: 
// Module Name:    instruction_fetch 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
module main_module(clk, reset, ALU_result);
input clk;
input reset;
output [31:0] ALU_result;

wire [3:0]ALU_control;
wire RegDst;
wire branch;
wire Memread;
wire MemtoReg;
wire MemWrite;
wire ALUSrc;
wire Regwrite;
wire Retcontrol;
wire reg_mem_in;


wire zflag;
wire carryflag;
wire signflag;
wire overflowflag;
wire ozflag;
wire ocarryflag;
wire osignflag;
wire ooverflowflag;

wire [7:0]pc_in;
wire [7:0]pci;
wire [7:0] pc_out;  //program_counter variables
wire [31:0] instr;
wire [7:0] add_out;
wire [4:0] reg_in;
wire [31:0] write_data;
wire [31:0] read_data1;
wire [31:0] read_data2;
wire [31:0] read_data;
wire [31:0] sign_out;
wire [31:0] alu_in;
wire [2:0] fmux_sel;
wire call_control;
wire b_instr_control;
wire out;
wire b_out;
wire [7:0]f_out;
wire [1:0]f_control;
wire out_m;

//Mux #(8) m(pci,8'b0,pc_in,reset);
program_counter pc (clk, reset, pc_in, pc_out);
instr_memory im (pc_out, clk, reset, instr);
adder a(pc_out,add_out);
control c(instr[31:26], ALU_control, RegDst,branch, Memread, MemtoReg, MemWrite, ALUSrc, Regwrite, Retcontrol);

Mux #(5) mux1 (instr[25:21],instr[20:16],reg_in,RegDst);  
reg_memory r(instr[25:21],reg_in,write_data,Regwrite,clk,reset,read_data1,read_data2,Memread);
Sign_Extension se(instr[15:0], sign_out);
Mux #(32) mux2 (read_data2,sign_out,alu_in,ALUSrc);      
ALU alu( read_data1, alu_in , ALU_control ,zflag ,carryflag, signflag,overflowflag , ALU_result );
delayflag df(zflag,signflag,carryflag,overflowflag,clk,reset,ozflag,osignflag,ocarryflag,ooverflowflag);
data_memory dm( clk, reset,ALU_result , read_data2, Memread, MemWrite, read_data);
Mux #(32) mux3(ALU_result, read_data,write_data,MemtoReg);


branchcontrol bc( instr[29:26], branch, call_control, fmux_sel, b_instr_control);
flag_mux fm(ozflag, ocarryflag, osignflag, ooverflowflag, fmux_sel, out );
Mux #(1) mux5(1'b0,out,out_m,branch);
Mux #(8) mux4(add_out,instr[7:0],f_out,out_m);
final_control fc(instr[31:30],out_m,Retcontrol,call_control,f_control);
final_out fo(f_out,instr[24:20],instr[7:0],call_control,add_out,f_control,pc_in,clk,reset);



endmodule



module reg_memory(read_reg1,read_reg2,write_data,reg_write,clk, reset,read_data1,read_data2,MemRead);
input [4:0] read_reg1 ;
 input [4:0] read_reg2;
 input [31:0] write_data;
input reg_write ;
input clk ;
input reset ;
output [31:0] read_data1 ;
output [31:0] read_data2;
input MemRead;

reg [31:0] regfile [31:0];
integer i;
assign read_data1 = regfile[read_reg1];
assign read_data2 = regfile[read_reg2];

always@(posedge clk  or posedge reset)
if(reset)
begin
	for(i=0;i<32;i=i+1)
		regfile[i]= 32'b0;     
end
else
begin
	if(reg_write)
		if(MemRead)
			regfile[read_reg2]= write_data;
		else regfile[read_reg1]= write_data;
end
endmodule

module Sign_Extension (sign_in, sign_out);
	input [15:0] sign_in;
	output [31:0] sign_out;
	assign sign_out[15:0]=sign_in[15:0];
	assign sign_out[31:16]=sign_in[15]?16'b1111_1111_1111_1111:16'b0;
endmodule

module program_counter(clk, reset, PC_in, PC_out);
	input clk, reset;
	input [7:0] PC_in;
	output reg [7:0] PC_out;
	always @ (posedge clk or posedge reset)
	begin
		if(reset==1'b1)
			PC_out=0;
		else
			PC_out=PC_in;
	end
endmodule

module Mux (in0, in1, mux_out, control);
	parameter N = 32;
	input [N-1:0] in0, in1;
	output [N-1:0] mux_out;
	input control;
	assign mux_out=control?in1:in0;
endmodule

//INSTRUCTION MEMORY
module instr_memory( addr ,clk,reset, instruction  );
input [7:0] addr ;
input reset;
input clk;
output [31:0] instruction; 

reg [31:0] instr_mem [255:0];
integer i;
assign instruction = instr_mem[addr];

always@(posedge clk or posedge reset)
begin
	if(reset==1)
	begin
		for(i=0;i<256;i=i+1)
			instr_mem[i]=32'b0;
	end
	else
	begin
	//BUBBLE SORT OF 4 NOS 111010, 111111, 110101, 001001
	instr_mem[0] = 32'b000000_00000_00000_0000000000000000;
	instr_mem[1] = 32'b010000_00001_00000_0000000000111010;
	instr_mem[2] = 32'b010000_00010_00000_0000000000111111;
	instr_mem[3] = 32'b010000_00011_00000_0000000000110101;
	instr_mem[4] = 32'b010000_00100_00000_0000000000001001;//store values in register first
	
	instr_mem[5] = 32'b110001_00000_00001_0000000000000001;
	instr_mem[6] = 32'b110001_00000_00010_0000000000000010;
	instr_mem[7] = 32'b110001_00000_00011_0000000000000011;
	instr_mem[8] = 32'b110001_00000_00100_0000000000000100; //then store in memory
	
	//sort now
	instr_mem[9] = 32'b010000_00101_00000_0000000000000100;
	instr_mem[10] = 32'b010000_00111_00000_0000000000000000; //i =0 t7 bb sort
	instr_mem[11]= 32'b000011_01000_01000_0000000000001100; //xor to make zero t8 =0 .loop1
	instr_mem[12]= 32'b000011_01001_01001_0000000000001100; //xor to make zero t9 =0
	instr_mem[13]= 32'b010000_00111_00000_0000000000000001; //i++
	instr_mem[14] =32'b000000_01000_00111_0000000000010000; //t8 = i
	instr_mem[15] =32'b000000_01001_00101_0000000000010000; //t9 = n 4 add
	instr_mem[16] =32'b000001_01001_01001_0000000000001000; // t9 = ~t9
	instr_mem[17] =32'b000000_01000_01001_0000000000010000; 	
	instr_mem[18] =32'b100110_00000_00000_0000000000101100;  // jump to end bns
	
	instr_mem[19] =32'b000011_01010_01010_0000000000001100; //xor t10 = 0
	
	instr_mem[20]= 32'b000011_01000_01000_0000000000001100; //xor to make zero t8 =0 .loop2
	instr_mem[21]= 32'b000011_01001_01001_0000000000001100; //xor to make zero t9 =0	
	
	instr_mem[22] =32'b010000_01010_00000_0000000000000001; //t10 +1 j = $10
	instr_mem[23] =32'b000000_01000_01010_0000000000010000; //t8+t10
	instr_mem[24] =32'b000000_01001_00101_0000000000010000; // t9 +t5
	instr_mem[25] =32'b000001_01001_01001_0000000000001000; //t9=~t9
	instr_mem[26] =32'b000000_01000_01001_0000000000010000; //add t8+ t9
	instr_mem[27] =32'b100110_00000_00000_0000000000001011;  // bns loop 1   goto11
	
	instr_mem[28]= 32'b000011_01000_01000_0000000000001100; //xor to make zero t8 =0 
	instr_mem[29]= 32'b000011_01001_01001_0000000000001100; //xor to make zero t9 =0	
	
	instr_mem[30]= 32'b000011_01101_01101_0000000000001100; //xor to make zero t13 =0
	instr_mem[31]= 32'b000000_01101_01010_0000000000010000; //add 
	instr_mem[32]= 32'b010000_01101_00000_0000000000000001; // j+1
	instr_mem[33]= 32'b110000_01101_01100_0000000000000000; // load $11=mem[j+1]
	instr_mem[34]= 32'b110000_01010_01011_0000000000000000; // load $12=mem[j]
	
	instr_mem[35] =32'b000000_01000_01011_0000000000010000; //t8=t11
	instr_mem[36] =32'b000000_01001_01100_0000000000010000; // t9 =t12	
	
	instr_mem[37] =32'b000001_01001_01001_0000000000001000; //t9=~t9
	instr_mem[38] =32'b000000_01000_01001_0000000000010000; //add t8+ t9
	instr_mem[39] =32'b100110_00000_00000_0000000000101001;  // bns swap
	instr_mem[40] =32'b100000_00000_00000_0000000000010100;  // j loop2
	
	instr_mem[41]= 32'b110001_01101_01011_0000000000000000; //swap st $t11 in mem[j] swap
	instr_mem[42]= 32'b110001_01010_01100_0000000000000000; //swap st $t12 in mem[j+1]
	
	instr_mem[43] =32'b100000_00000_00000_0000000000010100;  // j loop2
	
	//FINALLY ALL THE SORTED OUTPUTS ARE STORED IN DATA MEMORY IN REGISTERS 1,2,3,4

	end
end
endmodule



//ADDER FOR INSTRUCTION COUNT
module adder(curr_addr , PC);
   input [7:0] curr_addr;
	output [7:0] PC;
	assign PC = curr_addr + 8'b0000_0001;
endmodule



module ALU_add( input [7:0] pc ,input [32:0] se ,output [7:0] ou);
assign ou = pc + se[7:0];
endmodule



module ALU( read_data1, mux_data , ALU_control , zflag , carryflag, signflag, overflowflag ,ALU_result );
input [31:0] read_data1;
input [31:0] mux_data;
input [3:0] ALU_control;
output zflag;
output carryflag;
output signflag;
output overflowflag;
output reg [31:0] ALU_result;
reg zflag;
reg carryflag;
reg signflag;
reg overflowflag;

always@(*)
begin
 if(ALU_control[3:0]==4'b0000 || ALU_control[3:0]==4'b0111)                                                    // Add(i)
 begin
  {carryflag,ALU_result} = read_data1 + mux_data;
  
  overflowflag = (read_data1[31]&mux_data[31]&(~ALU_result[30])) |  ((~read_data1[31])&(~mux_data[31])&ALU_result[30]);
  end
 else if(ALU_control[3:0]==4'b0001)                                              // Complement
  ALU_result = ~mux_data+1'b1;
 else if(ALU_control[3:0]==4'b1000)                                              // Compi
  ALU_result = ~mux_data;
 else if(ALU_control[3:0]==4'b0010)                                              // And                  
  ALU_result = read_data1 & mux_data;
 else if(ALU_control[3:0]==4'b0011)                                              // XOR
  begin
   ALU_result = read_data1 ^ mux_data;
   if(ALU_result == 32'b0)
     zflag = 1'b0;
	else  
	  zflag = 1'b1;
  end  
 
 else if(ALU_control[3:0]==4'b0100 || ALU_control[3:0]==4'b1001)                                              // Shift left (variable)                             
     ALU_result = read_data1 << mux_data;	  
 
 else if(ALU_control[3:0]==4'b0101|| ALU_control[3:0]==4'b1010)                                              // Shift right (variable)                              
     ALU_result = read_data1 >> mux_data;	
 
 else if(ALU_control[3:0]==4'b0110|| ALU_control[3:0]==4'b1011)                                              // Shift right arithematic (variable)
     ALU_result = read_data1 >>> mux_data;
	  
 signflag = ALU_result[31];	  
end

endmodule


module data_memory( clk, reset, address, write_data, MemRead, MemWrite, read_data);
	input [31:0] address;
	input [31:0] write_data;
	input clk;
   input	reset;
   input	MemRead;
   input	MemWrite;
   output [31:0] read_data;
	wire [7:0]addr;
	
	reg [31:0] DMemory [255:0];
	integer k;
	
	assign addr=address[7:0];
	
	assign read_data = (MemRead) ? DMemory[addr] : 32'bx;

	always @(posedge clk or posedge reset)// Ou modifies reset to posedge
	begin
		if (reset == 1'b1) 
			begin
				for (k=0; k<256; k=k+1) begin
					DMemory[k] = 32'b0;
				end
			end
		else
			if (MemWrite == 1'b1) 
			    DMemory[addr] = write_data;
	end
endmodule

module control( opcode, ALU_control,RegDst,branch, MemRead, MemtoReg, MemWrite, ALUSrc, Regwrite, Retcontrol);
input [5:0] opcode;
output reg [3:0] ALU_control;
output reg RegDst;
output reg branch;
output reg MemRead;
output reg Retcontrol;
output reg MemWrite;
output reg ALUSrc;
output reg Regwrite;
output reg MemtoReg;

always@(*)
begin
 case(opcode[5:4])

 2'b00 : begin
			ALU_control = opcode[3:0];
			Regwrite=1'b1;
			RegDst=1'b1;
			branch=1'b0;
			MemRead=1'b0;
			Retcontrol=1'b0;
			MemWrite=1'b0;
			ALUSrc=1'b0;
			MemtoReg=1'b0;
			end
 2'b01 : begin
          if(opcode[3:0] == 4'b0101)
			  begin
			 Regwrite=1'b0;
			RegDst=1'b0;
			branch=1'b1;
			MemRead=1'b0;
			Retcontrol=1'b1;
			MemWrite=1'b0;
			ALUSrc=1'b0;
			MemtoReg=1'b0;
			 end
			 else if (opcode[3:0] == 4'b0110)
			 begin
			 Regwrite=1'b0;
			RegDst=1'b0;
			branch=1'b1;
			MemRead=1'b0;
			Retcontrol=1'b1;
			MemWrite=1'b0;
			ALUSrc=1'b0;
			MemtoReg=1'b0;
			end
			 else
			 begin
			 ALU_control = opcode[3:0]+4'b0111;
			 Regwrite=1'b1;
			RegDst=1'b0;
			branch=1'b0;
			MemRead=1'b0;
			Retcontrol=1'b0;
			MemWrite=1'b0;
			ALUSrc=1'b1;
			MemtoReg=1'b0;
			end
       end
  2'b10 : begin
          branch=1'b1;
			 Regwrite=1'b0;
			RegDst=1'b0;
			//branch=1'b0;
			MemRead=1'b0;
			Retcontrol=1'b0;
			MemWrite=1'b0;
			ALUSrc=1'b0;
			MemtoReg=1'b0;
	
         end
 2'b11 : begin
			RegDst=1'b1;
			ALU_control = 4'b0000;
         if(opcode[3:0]==4'b0000) 
			begin
			MemRead=1'b1;
			MemtoReg = 1'b1;
			Regwrite=1'b1;
			ALUSrc=1'b1;

			branch=1'b0;
			Retcontrol=1'b0;
			MemWrite=1'b0;
			end
			else if(opcode[3:0]==4'b0001)
			begin
			MemRead=1'b0;
			MemtoReg = 1'b0;
			Regwrite=1'b0;
			ALUSrc=1'b1;

			branch=1'b0;
			Retcontrol=1'b0;
			MemWrite=1'b1;
			end
       end			
 endcase 
 


end
endmodule

module final_control(flag,b,ret,call,out);
input [1:0]flag;
input b;
input ret;
input call;
output reg [1:0]out;
always@(*)
begin
if(b==1'b1)
out=2'b01;
else if(ret==1'b1)
out=2'b10;
else if(call==1'b1)
out=2'b11;
else
out=2'b00;
end
endmodule

module final_out(flag,ireg,addr,call_control,pc,sel,out,clk,reset);
input [7:0]flag;
input [4:0]ireg;
input [7:0]addr;
input [1:0]sel;
input call_control;
input [7:0]pc;
input clk;
input reset;
output reg [7:0]out;

wire [31:0]in;
wire [31:0]read_data1;
wire [31:0]read_data2;

assign in={24'b000000000000000000000000,pc[7:0]};

reg_memory reg_m(ireg,5'b10101,32'b0,1'b0,clk, reset,read_data1,read_data2);//reurn/br
reg_memory(5'b11111,read_reg2,in,call_control,clk, reset,read_data1,read_data2);//call
always@(*)
begin
case(sel)
00: out[7:0]=flag[7:0];
01: out[7:0]=addr[7:0];
10: out[7:0]=read_data1[7:0];
11: out[7:0]=addr[7:0];
endcase		
end

endmodule

module branchcontrol(  opcode, branch, call_control, fmux_sel, b_instr_control);
input [3:0] opcode;
input branch;
output reg call_control;
output reg [2:0] fmux_sel;
output reg b_instr_control;
always@(*)
begin
  if(branch == 1'b0)                                         // instructions other than branch instructions (10 instructions) 
   begin
	 call_control = 1'b0;
	 fmux_sel = 3'b000;
	 b_instr_control = 1'b0;
	end
  else if(branch == 1'b1)
   begin
	 if(opcode == 4'b0000)                               // b instr
	  begin
	   call_control = 1'b0;
	   fmux_sel = 3'b000;
	   b_instr_control = 1'b1;
	  end
	 else if(opcode == 4'b0001)                          // bz instr
	  begin 
	   call_control = 1'b0;
	   fmux_sel = 3'b111;
	   b_instr_control = 1'b0;
	  end
	 else if(opcode == 4'b0010)			    //  bnz instr
	  begin 
	   call_control = 1'b0;
	   fmux_sel = 3'b011;
	   b_instr_control = 1'b0;
	  end 
	 else if(opcode == 4'b0011)			    //  bcy instr
	  begin 
	   call_control = 1'b0;
	   fmux_sel = 3'b101;
	   b_instr_control = 1'b0;
	  end
    else if(opcode == 4'b0100)                              // bncy instr
	  begin
           call_control = 1'b0;
	   fmux_sel = 3'b001;
	   b_instr_control = 1'b010;	  
	  end	
    else if(opcode == 4'b0101)                          // bs instr
	  begin 
	   call_control = 1'b0;
	   fmux_sel = 3'b110;
	   b_instr_control = 1'b0;
	  end 
    else if(opcode == 4'b0110)	                              // bns instr
	  begin 
	   call_control = 1'b0;
	   fmux_sel = 3'b010;
	   b_instr_control = 1'b0;
	  end
    else if(opcode == 4'b0111)                              // bv instr
	  begin
    	   call_control = 1'b0;
	   fmux_sel = 3'b100;
	   b_instr_control = 1'b0;	  
	  end
    else if(opcode == 4'b1000)                              // bnv instr
	  begin
     	   call_control = 1'b0;
	   fmux_sel = 3'b000;
	   b_instr_control = 1'b0;	  
	  end
    else if(opcode == 4'b1001)                              // call instr
	  begin
      	   call_control = 1'b1;
	   fmux_sel = 3'b000;
	   b_instr_control = 1'b0;	  
	  end	  
   end	
end

endmodule

module delayflag( input a,input b ,input c ,input d ,input clk,
input reset, output reg na,output reg nb,output reg nc ,output reg nd);
always@(posedge clk or posedge reset)
begin
	if(reset ==1)
		begin
			na = 1'b0;
			nb = 1'b0;
			nc = 1'b0;
			nd = 1'b0;
		end
	else
		begin
			na = a;
			nb = b;
			nc = c;
			nd = d;		
		end
end
endmodule

module flag_mux(zflag, carryflag, signflag, oflowflag, control, out );
input zflag;
input carryflag;
input signflag;
input oflowflag;
input [2:0] control;
output reg out;
always@(*)
begin
case(control)
3'b000 : out = ~oflowflag;
3'b001 : out = ~carryflag;
3'b010 : out = ~signflag;
3'b011 : out = ~zflag;
3'b100 : out = oflowflag;
3'b101 : out = carryflag;
3'b110 : out = signflag;
3'b111 : out = zflag;
endcase
end

endmodule







