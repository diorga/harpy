`include "cci_mpf_test_conf_default.vh"
`include "cci_mpf_if.vh"
`include "cci_test_csrs.vh"

// Generated from the AFU JSON file by afu_json_mgr
`include "afu_json_info.vh"

 `define NOP             0
 `define WR_REQ          1
 `define WR_RSP          2
 `define RD_REQ          3
 `define RD_RSP          4
 `define FN_REQ          5
 `define FN_RSP          6

 `define X_ADDR          0
 `define Y_ADDR          1
 `define Z_ADDR          2

 `define INSTR_LENGTH    13


module counter
    #(
     parameter SIZE = 12
    )
    (
     input logic clk,
     input logic reset,
     input logic enable,
     input logic [SIZE-1:0] limit,
     output logic reached
    );

    logic [SIZE-1:0] counter;

    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            counter <= 0;
            reached <= 0;
        end
        else if ((counter == limit) && enable)
        begin
            counter <= 0;
            reached <= 1;
        end
        else if (enable)
        begin
            counter <= counter + 4'd1;
            reached <= 0;
        end
    end

endmodule



module test_afu
   (
    input  logic clk,

    // Connection toward the host.  Reset comes in here.
    cci_mpf_if.to_fiu fiu,

    // CSR connections
    test_csrs.test csrs,

    // MPF tracks outstanding requests.  These will be true as long as
    // reads or unacknowledged writes are still in flight.
    input logic c0NotEmpty,
    input logic c1NotEmpty
    );

    // Local reset to reduce fan-out
    logic reset = 1'b1;
    always @(posedge clk)
    begin
        reset <= fiu.reset;
    end


    //
    // Convert between byte addresses and line addresses.  The conversion
    // is simple: adding or removing low zero bits.
    //

    localparam CL_BYTE_IDX_BITS = 6;
    typedef logic [$bits(t_cci_clAddr) + CL_BYTE_IDX_BITS - 1 : 0] t_byteAddr;

    function automatic t_cci_clAddr byteAddrToClAddr(t_byteAddr addr);
        return addr[CL_BYTE_IDX_BITS +: $bits(t_cci_clAddr)];
    endfunction

    function automatic t_byteAddr clAddrToByteAddr(t_cci_clAddr addr);
        return {addr, CL_BYTE_IDX_BITS'(0)};
    endfunction


    // ====================================================================
    //
    //  CSRs (simple connections to the external CSR management engine)
    //
    // ====================================================================
    typedef logic [63 : 0] t_counter;

    t_counter exp_count;

    // CSR info
    t_counter cnt_rd_rsp;
    t_counter cnt_wr_rsp;



    always_comb
    begin
        // The AFU ID is a unique ID for a given program.  Here we generated
        // one with the "uuidgen" program and stored it in the AFU's JSON file.
        // ASE and synthesis setup scripts automatically invoke afu_json_mgr
        // to extract the UUID into afu_json_info.vh.
        csrs.afu_id = `AFU_ACCEL_UUID;

        // Default
        for (int i = 0; i < NUM_TEST_CSRS; i = i + 1)
        begin
            csrs.cpu_rd_csrs[i].data = 64'(0);
        end

        // Number of reads responses
        csrs.cpu_rd_csrs[4].data = 64'(cnt_rd_rsp);

        // Number of completed writes
        csrs.cpu_rd_csrs[5].data = 64'(cnt_wr_rsp);

    end


    //
    // Consume configuration CSR writes
    //

    // Memory address to which this AFU will write the result
    t_ccip_clAddr x_addr;
    t_ccip_clAddr y_addr;
    t_ccip_clAddr z_addr;
    t_ccip_clAddr read_registers_addr;
    t_ccip_clAddr valid_addr;
    t_ccip_clAddr finish_addr;
    t_counter total_exp;
    logic [7:0] vl0_enemy;
    logic [7:0] vh0_enemy;
    logic [7:0] vh1_enemy;

    logic [127:0] instr_mem;

    logic [2:0] instr_0, instr_1, instr_2, instr_3, instr_4, instr_5, instr_6, instr_7;
    logic [1:0] instr_addr_0, instr_addr_1, instr_addr_2, instr_addr_3, instr_addr_4, instr_addr_5, instr_addr_6, instr_addr_7;
    logic [1:0] instr_channel_0, instr_channel_1, instr_channel_2, instr_channel_3, instr_channel_4, instr_channel_5, instr_channel_6, instr_channel_7;
    logic [2:0] instr_mdata_0, instr_mdata_1, instr_mdata_2, instr_mdata_3, instr_mdata_4, instr_mdata_5, instr_mdata_6, instr_mdata_7;
    logic [2:0] instr_value_0, instr_value_1, instr_value_2, instr_value_3, instr_value_4, instr_value_5, instr_value_6, instr_value_7;

    // CSR 0 triggers start
    logic start;

    always_ff @(posedge clk)
    begin
        if (reset)
        begin
          x_addr                <= 0;
          y_addr                <= 0;
          z_addr                <= 0;
          read_registers_addr   <= 0;
          valid_addr            <= 0;
          finish_addr           <= 0;
          vl0_enemy             <= 0;
          vh0_enemy             <= 0;
          vh1_enemy             <= 0;
          total_exp             <= 0;
        end

        start <= csrs.cpu_wr_csrs[0].en;

        if (csrs.cpu_wr_csrs[1].en)
        begin
            x_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[1].data);
            $display(" x buffer at VA 0x%x", csrs.cpu_wr_csrs[1].data );
        end
        if (csrs.cpu_wr_csrs[2].en)
        begin
            y_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[2].data);
            $display(" y buffer at VA 0x%x", csrs.cpu_wr_csrs[2].data );
        end
        if (csrs.cpu_wr_csrs[3].en)
        begin
            z_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[3].data);
            $display(" z buffer at VA 0x%x", csrs.cpu_wr_csrs[3].data );
        end
        if (csrs.cpu_wr_csrs[4].en)
        begin
            read_registers_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[4].data);
            $display(" read registers buffer at VA 0x%x", csrs.cpu_wr_csrs[4].data );
        end
        if (csrs.cpu_wr_csrs[5].en)
        begin
            valid_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[5].data);
            $display(" ok buffer at VA 0x%x", csrs.cpu_wr_csrs[5].data );
        end
        if (csrs.cpu_wr_csrs[6].en)
        begin
            finish_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[6].data);
            $display(" finish buffer at VA 0x%x", csrs.cpu_wr_csrs[6].data );
        end

        if (csrs.cpu_wr_csrs[7].en)
        begin
            vl0_enemy <= csrs.cpu_wr_csrs[7].data;
            $display(" VL0 enemy will be triggered every %d times", csrs.cpu_wr_csrs[7].data );
        end
        if (csrs.cpu_wr_csrs[8].en)
        begin
            vh0_enemy <= csrs.cpu_wr_csrs[8].data;
            $display(" VH0 enemy will be triggered every %d times", csrs.cpu_wr_csrs[8].data );
        end
        if (csrs.cpu_wr_csrs[9].en)
        begin
            vh1_enemy <= csrs.cpu_wr_csrs[9].data;
            $display(" VH1 enemy will be triggered every %d times", csrs.cpu_wr_csrs[9].data );
        end

        if (csrs.cpu_wr_csrs[10].en)
        begin
            total_exp <= csrs.cpu_wr_csrs[10].data;
            $display(" Repeating the experiment %d times", csrs.cpu_wr_csrs[10].data );
        end
        if (csrs.cpu_wr_csrs[11].en)
        begin
            instr_0         <= csrs.cpu_wr_csrs[11].data[2:0];
            instr_addr_0    <= csrs.cpu_wr_csrs[11].data[4:3];
            instr_channel_0 <= csrs.cpu_wr_csrs[11].data[6:5];
            instr_mdata_0   <= csrs.cpu_wr_csrs[11].data[9:7];
            instr_value_0   <= csrs.cpu_wr_csrs[11].data[12:10];
            instr_1         <= csrs.cpu_wr_csrs[11].data[15:13];
            instr_addr_1    <= csrs.cpu_wr_csrs[11].data[17:16];
            instr_channel_1 <= csrs.cpu_wr_csrs[11].data[19:18];
            instr_mdata_1   <= csrs.cpu_wr_csrs[11].data[22:20];
            instr_value_1   <= csrs.cpu_wr_csrs[11].data[25:23];
            $display(" Event 0 instr %d ",    csrs.cpu_wr_csrs[11].data[2:0]);
            $display(" Event 0 ADDR %d ",     csrs.cpu_wr_csrs[11].data[4:3]);
            $display(" Event 0 CHANNEL %d ",  csrs.cpu_wr_csrs[11].data[6:5]);
            $display(" Event 0 MDATA %d ",    csrs.cpu_wr_csrs[11].data[9:7]);
            $display(" Event 0 VALUE %d ",    csrs.cpu_wr_csrs[11].data[12:10]);
            $display(" Event 1 instr %d ",    csrs.cpu_wr_csrs[11].data[15:13]);
            $display(" Event 1 ADDR %d ",     csrs.cpu_wr_csrs[11].data[17:16]);
            $display(" Event 1 CHANNEL %d ",  csrs.cpu_wr_csrs[11].data[19:18]);
            $display(" Event 1 MDATA %d ",    csrs.cpu_wr_csrs[11].data[22:20]);
            $display(" Event 1 VALUE %d ",    csrs.cpu_wr_csrs[11].data[25:23]);
        end
        if (csrs.cpu_wr_csrs[12].en)
        begin
            instr_2         <= csrs.cpu_wr_csrs[12].data[2:0];
            instr_addr_2    <= csrs.cpu_wr_csrs[12].data[4:3];
            instr_channel_2 <= csrs.cpu_wr_csrs[12].data[6:5];
            instr_mdata_2   <= csrs.cpu_wr_csrs[12].data[9:7];
            instr_value_2   <= csrs.cpu_wr_csrs[12].data[12:10];
            instr_3         <= csrs.cpu_wr_csrs[12].data[15:13];
            instr_addr_3    <= csrs.cpu_wr_csrs[12].data[17:16];
            instr_channel_3 <= csrs.cpu_wr_csrs[12].data[19:18];
            instr_mdata_3   <= csrs.cpu_wr_csrs[12].data[22:20];
            instr_value_3   <= csrs.cpu_wr_csrs[12].data[25:23];
            $display(" Event 2 instr %d ",    csrs.cpu_wr_csrs[12].data[2:0]);
            $display(" Event 2 ADDR %d ",     csrs.cpu_wr_csrs[12].data[4:3]);
            $display(" Event 2 CHANNEL %d ",  csrs.cpu_wr_csrs[12].data[6:5]);
            $display(" Event 2 MDATA %d ",    csrs.cpu_wr_csrs[12].data[9:7]);
            $display(" Event 2 VALUE %d ",    csrs.cpu_wr_csrs[12].data[12:10]);
            $display(" Event 3 instr %d ",    csrs.cpu_wr_csrs[12].data[15:13]);
            $display(" Event 3 ADDR %d ",     csrs.cpu_wr_csrs[12].data[17:16]);
            $display(" Event 3 CHANNEL %d ",  csrs.cpu_wr_csrs[12].data[19:18]);
            $display(" Event 3 MDATA %d ",    csrs.cpu_wr_csrs[12].data[22:20]);
            $display(" Event 3 VALUE %d ",    csrs.cpu_wr_csrs[12].data[25:23]);
        end
        if (csrs.cpu_wr_csrs[13].en)
        begin
            instr_4         <= csrs.cpu_wr_csrs[13].data[2:0];
            instr_addr_4    <= csrs.cpu_wr_csrs[13].data[4:3];
            instr_channel_4 <= csrs.cpu_wr_csrs[13].data[6:5];
            instr_mdata_4   <= csrs.cpu_wr_csrs[13].data[9:7];
            instr_value_4   <= csrs.cpu_wr_csrs[13].data[12:10];
            instr_5         <= csrs.cpu_wr_csrs[13].data[15:13];
            instr_addr_5    <= csrs.cpu_wr_csrs[13].data[17:16];
            instr_channel_5 <= csrs.cpu_wr_csrs[13].data[19:18];
            instr_mdata_5   <= csrs.cpu_wr_csrs[13].data[22:20];
            instr_value_5   <= csrs.cpu_wr_csrs[13].data[25:23];
            $display(" Event 4 instr %d ",    csrs.cpu_wr_csrs[13].data[2:0]);
            $display(" Event 4 ADDR %d ",     csrs.cpu_wr_csrs[13].data[4:3]);
            $display(" Event 4 CHANNEL %d ",  csrs.cpu_wr_csrs[13].data[6:5]);
            $display(" Event 4 MDATA %d ",    csrs.cpu_wr_csrs[13].data[9:7]);
            $display(" Event 4 VALUE %d ",    csrs.cpu_wr_csrs[13].data[12:10]);
            $display(" Event 5 instr %d ",    csrs.cpu_wr_csrs[13].data[15:13]);
            $display(" Event 5 ADDR %d ",     csrs.cpu_wr_csrs[13].data[17:16]);
            $display(" Event 5 CHANNEL %d ",  csrs.cpu_wr_csrs[13].data[19:18]);
            $display(" Event 5 MDATA %d ",    csrs.cpu_wr_csrs[13].data[22:20]);
            $display(" Event 5 VALUE %d ",    csrs.cpu_wr_csrs[13].data[25:23]);
        end
        if (csrs.cpu_wr_csrs[14].en)
        begin
            instr_6         <= csrs.cpu_wr_csrs[14].data[2:0];
            instr_addr_6    <= csrs.cpu_wr_csrs[14].data[4:3];
            instr_channel_6 <= csrs.cpu_wr_csrs[14].data[6:5];
            instr_mdata_6   <= csrs.cpu_wr_csrs[14].data[9:7];
            instr_value_6   <= csrs.cpu_wr_csrs[14].data[12:10];
            instr_7         <= csrs.cpu_wr_csrs[14].data[15:13];
            instr_addr_7    <= csrs.cpu_wr_csrs[14].data[17:16];
            instr_channel_7 <= csrs.cpu_wr_csrs[14].data[19:18];
            instr_mdata_7   <= csrs.cpu_wr_csrs[14].data[22:20];
            instr_value_7   <= csrs.cpu_wr_csrs[14].data[25:23];
            $display(" Event 6 instr %d ",    csrs.cpu_wr_csrs[14].data[2:0]);
            $display(" Event 6 ADDR %d ",     csrs.cpu_wr_csrs[14].data[4:3]);
            $display(" Event 6 CHANNEL %d ",  csrs.cpu_wr_csrs[14].data[6:5]);
            $display(" Event 6 MDATA %d ",    csrs.cpu_wr_csrs[14].data[9:7]);
            $display(" Event 6 VALUE %d ",    csrs.cpu_wr_csrs[14].data[12:10]);
            $display(" Event 7 instr %d ",    csrs.cpu_wr_csrs[14].data[15:13]);
            $display(" Event 7 ADDR %d ",     csrs.cpu_wr_csrs[14].data[17:16]);
            $display(" Event 7 CHANNEL %d ",  csrs.cpu_wr_csrs[14].data[19:18]);
            $display(" Event 7 MDATA %d ",    csrs.cpu_wr_csrs[14].data[22:20]);
            $display(" Event 7 VALUE %d ",    csrs.cpu_wr_csrs[14].data[25:23]);
        end
    end


    t_ccip_clAddr instr_address_0, instr_address_1, instr_address_2, instr_address_3, instr_address_4, instr_address_5, instr_address_6, instr_address_7;

    // Go from address index to actual address received
    always_ff @(posedge clk)
    begin
      case(instr_addr_0)                // address
          0:                            // X_ADDR
          begin
              instr_address_0    <= x_addr;
          end
          1:                            // Y_ADDR
          begin
              instr_address_0    <= y_addr;
          end
          2:                            // Z_ADDR
          begin
              instr_address_0    <= z_addr;
          end
      endcase
      case(instr_addr_1)                // address
          0:                            // X_ADDR
          begin
              instr_address_1    <= x_addr;
          end
          1:                            // Y_ADDR
          begin
              instr_address_1    <= y_addr;
          end
          2:                            // Z_ADDR:
          begin
              instr_address_1    <= z_addr;
          end
      endcase
      case(instr_addr_2)                // address
          0:                            // X_ADDR
          begin
              instr_address_2    <= x_addr;
          end
          1:                            // Y_ADDR
          begin
              instr_address_2    <= y_addr;
          end
          2:                            // Z_ADDR:
          begin
              instr_address_2    <= z_addr;
          end
      endcase
      case(instr_addr_3)                // address
          0:                            // X_ADDR:
          begin
              instr_address_3    <= x_addr;
          end
          1:                            // Y_ADDR:
          begin
              instr_address_3    <= y_addr;
          end
          2:                            // Z_ADDR:
          begin
              instr_address_3    <= z_addr;
          end
      endcase
      case(instr_addr_4)                // address
          0:                            // X_ADDR:
          begin
              instr_address_4    <= x_addr;
          end
          1:                            // Y_ADDR:
          begin
              instr_address_4    <= y_addr;
          end
          2:                            // Z_ADDR:
          begin
              instr_address_4    <= z_addr;
          end
      endcase
      case(instr_addr_5)                // address
          0:                            // X_ADDR:
          begin
              instr_address_5    <= x_addr;
          end
          1:                            // Y_ADDR:
          begin
              instr_address_5    <= y_addr;
          end
          2:                            // Z_ADDR:
          begin
              instr_address_5    <= z_addr;
          end
      endcase
      case(instr_addr_6)                // address
          0:                            // X_ADDR:
          begin
              instr_address_6    <= x_addr;
          end
          1:                            // Y_ADDR:
          begin
              instr_address_6    <= y_addr;
          end
          2:                            // Z_ADDR:
          begin
              instr_address_6    <= z_addr;
          end
      endcase
      case(instr_addr_7)                // address
          0:                            // X_ADDR:
          begin
              instr_address_7    <= x_addr;
          end
          1:                            // Y_ADDR:
          begin
              instr_address_7    <= y_addr;
          end
          2:                            // Z_ADDR:
          begin
              instr_address_7    <= z_addr;
          end
      endcase
    end



    logic [4:0] pc;

    logic [2:0] instr;
    t_ccip_clAddr instr_addr;
    logic [1:0] instr_channel;
    logic [2:0] instr_mdata;
    logic [2:0] instr_value;

    // This is basically the instruction STATE_FETCH
    always_ff @(posedge clk)
    begin
      if (reset)
      begin
        instr <= 0;
        instr_addr <= 0;
        instr_channel <= 0;
        instr_mdata <= 0;
        instr_value <= 0;
      end else begin
      case(pc)
      0:
      begin
          instr <= instr_0;
          instr_addr <= instr_address_0;
          instr_channel <= instr_channel_0;
          instr_mdata <= instr_mdata_0;
          instr_value <= instr_value_0;
      end
      1:
      begin
          instr <= instr_1;
          instr_addr <= instr_address_1;
          instr_channel <= instr_channel_1;
          instr_mdata <= instr_mdata_1;
          instr_value <= instr_value_1;
      end
      2:
      begin
          instr <= instr_2;
          instr_addr <= instr_address_2;
          instr_channel <= instr_channel_2;
          instr_mdata <= instr_mdata_2;
          instr_value <= instr_value_2;
      end
      3:
      begin
          instr <= instr_3;
          instr_addr <= instr_address_3;
          instr_channel <= instr_channel_3;
          instr_mdata <= instr_mdata_3;
          instr_value <= instr_value_3;
      end
      4:
      begin
          instr <= instr_4;
          instr_addr <= instr_address_4;
          instr_channel <= instr_channel_4;
          instr_mdata <= instr_mdata_4;
          instr_value <= instr_value_4;
      end
      5:
      begin
          instr <= instr_5;
          instr_addr <= instr_address_5;
          instr_channel <= instr_channel_5;
          instr_mdata <= instr_mdata_5;
          instr_value <= instr_value_5;
      end
      6:
      begin
          instr <= instr_6;
          instr_addr <= instr_address_6;
          instr_channel <= instr_channel_6;
          instr_mdata <= instr_mdata_6;
          instr_value <= instr_value_6;
      end
      7:
      begin
          instr <= instr_7;
          instr_addr <= instr_address_7;
          instr_channel <= instr_channel_7;
          instr_mdata <= instr_mdata_7;
          instr_value <= instr_value_7;
      end
      endcase
      end
    end


    // =========================================================================
    //
    //   State machines
    //
    // =========================================================================

//    logic fetch_finished;
    logic write_req_finished;
    logic read_req_finished;
    logic fence_req_finished;
    logic write_rsp_finished;
    logic read_rsp_finished;
    logic fence_rsp_finished;
    logic write_back_finished;
    logic write_valid_finished;
    logic finish_finished;
    logic final_fence_finished;
    logic final_fence_rsp_finished;

    logic [511:0] write_valid_data;

    t_counter writes_received;
    t_counter reads_received;
    t_counter writes_issued;
    t_counter reads_issued;


    typedef enum logic [4:0]
    {
        STATE_IDLE,
        STATE_NEW_EXPERIMENT,
        STATE_FETCH,
        STATE_DECODE,
        STATE_WRITE_REQ,
        STATE_READ_REQ,
        STATE_READ_RSP,
        STATE_FENCE_REQ,
        STATE_WRITE_RSP,
        STATE_FENCE_RSP,
        STATE_INC_PC,
        STATE_WRITE_BACK,
        STATE_WRITE_VALID,
        STATE_WAIT_RESPONSES,
        STATE_FINISH,
        STATE_FINAL_FENCE,
        STATE_FINAL_FENCE_RSP
    }
    t_state;
    t_state thread_state;

    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            thread_state <= STATE_IDLE;
            exp_count <= 0;
            pc <= 0;
        end
        else
        begin
            case (thread_state)
                STATE_IDLE:
                begin
                    exp_count <= 0;
                    pc <= 0;
                    if (start)
                    begin
                        $display(" STATE_NEW_EXPERIMENT" );
                        thread_state <= STATE_NEW_EXPERIMENT;
                    end
                end

                STATE_NEW_EXPERIMENT:
                begin
                    $display(" STATE_FETCH" );
                    pc <= 0;
                    thread_state <= STATE_FETCH;
                end

                STATE_FETCH:
                begin
                    $display(" STATE_DECODE" );
                    thread_state <= STATE_DECODE;
                end

                STATE_DECODE:
                begin
                    case (instr)
                      0:                            // NOP:
                      begin
                        $display(" STATE_INC_PC" );
                        thread_state <= STATE_INC_PC;
                      end
                      1:                            // WR_REQ:
                      begin
                        $display(" STATE_WRITE_REQ" );
                        thread_state <= STATE_WRITE_REQ;
                      end
                      2:                            // WR_RSP:
                      begin
                        $display(" STATE_WRITE_RSP" );
                        thread_state <= STATE_WRITE_RSP;
                      end
                      3:                            // RD_REQ:
                      begin
                        $display(" STATE_READ_REQ" );
                        thread_state <= STATE_READ_REQ;
                      end
                      4:                            // RD_RSP:
                      begin
                        $display(" STATE_READ_RSP" );
                        thread_state <= STATE_READ_RSP;
                      end
                      5:                            // FN_REQ:
                      begin
                        $display(" STATE_FENCE_REQ" );
                        thread_state <= STATE_FENCE_REQ;
                      end
                      6:                            // FN_RSP:
                      begin
                        $display(" STATE_FENCE_RSP" );
                        thread_state <= STATE_FENCE_RSP;
                      end
                    endcase
                end

                STATE_WRITE_REQ:
                begin
                    if (write_req_finished)
                    begin
                        $display(" STATE_INC_PC" );
                        thread_state <= STATE_INC_PC;
                    end
                end

                STATE_WRITE_RSP:
                begin
                    if ((write_rsp_finished) || (!write_valid_data))
                    begin
                        $display(" STATE_INC_PC" );
                        thread_state <= STATE_INC_PC;
                    end
                end

                STATE_READ_REQ:
                begin
                    if (read_req_finished)
                    begin
                        $display(" STATE_INC_PC" );
                        thread_state <= STATE_INC_PC;
                    end
                end

                STATE_READ_RSP:
                begin
                    if ((read_rsp_finished) || (!write_valid_data))
                    begin
                        $display(" STATE_INC_PC" );
                        thread_state <= STATE_INC_PC;
                    end
                end

                STATE_FENCE_REQ:
                begin
                    if (fence_req_finished)
                    begin
                        $display(" STATE_INC_PC" );
                        thread_state <= STATE_INC_PC;
                    end
                end

                STATE_FENCE_RSP:
                begin
                    if ((fence_rsp_finished) || (!write_valid_data))
                    begin
                        $display(" STATE_INC_PC" );
                        thread_state <= STATE_INC_PC;
                    end
                end

                STATE_INC_PC:
                begin
                  if ((pc == 7) || (!write_valid_data))
                  begin
                        $display(" STATE_WRITE_BACK" );
                        thread_state <= STATE_WRITE_BACK;
                  end else begin
                        $display(" STATE_FETCH" );
                        thread_state <= STATE_FETCH;
                  end
                  pc <= (pc + 1) % 8;
                end

                STATE_WRITE_BACK:
                begin
                    if (write_back_finished)
                    begin
                        $display(" STATE_WRITE_VALID" );
                        thread_state <= STATE_WRITE_VALID;
                    end
                end

                STATE_WRITE_VALID:
                begin
                    if (write_valid_finished)
                    begin
                      exp_count <= exp_count + 1;
                      $display(" STATE_WAIT_RESPONSES" );
                      thread_state <= STATE_WAIT_RESPONSES;
                    end
                end

                STATE_WAIT_RESPONSES:
                begin
                    if ((writes_issued == writes_received) &&
                       (reads_issued == reads_received))
                    begin
                      if (exp_count <= total_exp)
                      begin
                        $display(" STATE_NEW_EXPERIMENT" );
                        thread_state <= STATE_NEW_EXPERIMENT;
                      end else begin
                        $display(" STATE_FINISH" );
                        thread_state <= STATE_FINISH;
                      end
                    end
                end

                STATE_FINISH:
                begin
                    if (finish_finished)
                    begin
                        $display(" STATE_FINAL_FENCE" );
                        thread_state <= STATE_FINAL_FENCE;
                    end
                end

                STATE_FINAL_FENCE:
                begin
                    if (final_fence_finished)
                    begin
                        $display(" STATE_FINAL_FENCE_RSP" );
                        thread_state <= STATE_FINAL_FENCE_RSP;
                    end
                end

                STATE_FINAL_FENCE_RSP:
                begin
                    if (final_fence_rsp_finished)
                    begin
                        $display(" STATE_IDLE" );
                        thread_state <= STATE_IDLE;
                    end
                end


            endcase
        end
    end

    /// ====================================
    ///
    ///    Write logic
    ///
    /// ====================================
    t_cci_mpf_ReqMemHdrParams wr_params_write_req;
    t_cci_mpf_ReqMemHdrParams wr_params_fence_req;
    t_cci_mpf_ReqMemHdrParams wr_params_write_back;
    t_cci_mpf_ReqMemHdrParams wr_params_write_valid;
    t_cci_mpf_ReqMemHdrParams wr_params_finished;
    t_cci_mpf_ReqMemHdrParams wr_params_final_fence;

    t_cci_mpf_ReqMemHdrParams wr_params_vl0;
    t_cci_mpf_ReqMemHdrParams wr_params_vh0;
    t_cci_mpf_ReqMemHdrParams wr_params_vh1;




    always_comb
    begin
        // Address is virtual or not
        wr_params_write_req = cci_mpf_defaultReqHdrParams(1);
        wr_params_fence_req = cci_mpf_defaultReqHdrParams(1);
        wr_params_write_back = cci_mpf_defaultReqHdrParams(1);
        wr_params_write_valid = cci_mpf_defaultReqHdrParams(1);
        wr_params_finished = cci_mpf_defaultReqHdrParams(1);
        wr_params_final_fence = cci_mpf_defaultReqHdrParams(1);

        wr_params_vl0 = cci_mpf_defaultReqHdrParams(1);
        wr_params_vh0 = cci_mpf_defaultReqHdrParams(1);
        wr_params_vh1 = cci_mpf_defaultReqHdrParams(1);

        // Write channel
        wr_params_write_req.vc_sel = t_ccip_vc'(instr_channel);
        wr_params_fence_req.vc_sel = t_ccip_vc'(instr_channel);

//        wr_params_write_back.vc_sel = eVC_VL0;
//        wr_params_write_valid.vc_sel = eVC_VL0;
//        wr_params_finished.vc_sel = eVC_VL0;

        wr_params_vl0.vc_sel = eVC_VL0;
        wr_params_vh0.vc_sel = eVC_VH0;
        wr_params_vh1.vc_sel = eVC_VH1;


    end


    t_cci_mpf_c1_ReqMemHdr wr_hdr_write_req;
//    t_cci_mpf_c1_ReqMemHdr wr_hdr_fence_req;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_write_back;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_write_valid;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_finished;

    t_cci_mpf_c1_ReqMemHdr wr_hdr_vl0;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_vh0;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_vh1;

    assign wr_hdr_write_req = cci_mpf_c1_genReqHdr(eREQ_WRLINE_I,
                                          instr_addr + exp_count,
                                          t_cci_mdata'(instr_mdata),
                                          wr_params_write_req);

    assign wr_hdr_write_back = cci_mpf_c1_genReqHdr(eREQ_WRLINE_I,
                                          read_registers_addr + exp_count,
                                          t_cci_mdata'(15),
                                          wr_params_write_back);

    assign wr_hdr_write_valid = cci_mpf_c1_genReqHdr(eREQ_WRLINE_I,
                                          valid_addr + exp_count,
                                          t_cci_mdata'(16),
                                          wr_params_write_valid);


    assign wr_hdr_finished = cci_mpf_c1_genReqHdr(eREQ_WRLINE_I,
                                          finish_addr,
                                          t_cci_mdata'(18),
                                          wr_params_finished);




    assign wr_hdr_vl0 = cci_mpf_c1_genReqHdr(eREQ_WRLINE_I,
                                             finish_addr + 1,
                                             t_cci_mdata'(20),
                                             wr_params_vl0);

    assign wr_hdr_vh0 = cci_mpf_c1_genReqHdr(eREQ_WRLINE_I,
                                             finish_addr + 1,
                                             t_cci_mdata'(21),
                                             wr_params_vh0);

    assign wr_hdr_vh1 = cci_mpf_c1_genReqHdr(eREQ_WRLINE_I,
                                             finish_addr + 2,
                                             t_cci_mdata'(22),
                                             wr_params_vh1);



    logic r_vl0_enemy;
    counter
    #(
    .SIZE(8)
    )
    counter_vl0
    (
    .clk(clk),
    .reset(reset),
    .enable(vl0_enemy > 0),
    .limit(vl0_enemy),
    .reached(r_vl0_enemy)
    );

    logic r_vh0_enemy;
    counter
    #(
    .SIZE(8)
    )
    counter_vh0
    (
    .clk(clk),
    .reset(reset),
    .enable(vh0_enemy > 0),
    .limit(vh0_enemy),
    .reached(r_vh0_enemy)
   );

    logic r_vh1_enemy;
    counter
    #(
    .SIZE(8)
    )
    counter_vh1
    (
    .clk(clk),
    .reset(reset),
    .enable(vh1_enemy > 0),
    .limit(vh1_enemy),
    .reached(r_vh1_enemy)
    );

    logic [511:0] write_back_data;

    // Data to send
    always_ff @(posedge clk)
    begin
        if (thread_state == STATE_WRITE_REQ)
        begin
            fiu.c1Tx.data <= t_ccip_clData'({509'h0, instr_value});
        end
        else if (thread_state == STATE_WRITE_BACK)
        begin
            fiu.c1Tx.data <= t_ccip_clData'(write_back_data);
        end
        else if (thread_state == STATE_WRITE_VALID)
        begin
            fiu.c1Tx.data <= t_ccip_clData'(write_valid_data);
        end
        else if (thread_state == STATE_FINISH)
        begin
            fiu.c1Tx.data <= t_ccip_clData'(512'h1);
        end
        else
        begin
            fiu.c1Tx.data <= t_ccip_clData'(512'h1);  // Enemy should be 1
        end
    end


    // Write request
    // This controls fiu.c1TX.hdr && fiu.c1Tx.valid
    always_ff @(posedge clk)
    begin
        if (reset || thread_state == STATE_NEW_EXPERIMENT)
        begin
            fiu.c1Tx.valid <= 1'b0;
            write_req_finished <= 1'b0;
            fence_req_finished <= 1'b0;
            write_back_finished <= 1'b0;
            write_valid_finished <= 1'b0;
            finish_finished <= 1'b0;
            final_fence_finished <= 1'b0;
            writes_issued <= t_counter'(0);
        end
        else if ( (thread_state == STATE_WRITE_REQ) &&
                (!fiu.c1TxAlmFull) &&
                (!write_req_finished) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_write_req;
            fiu.c1Tx.valid <= (thread_state == STATE_WRITE_REQ) &&
                                (!fiu.c1TxAlmFull) &&
                              (!write_req_finished) ;
            write_req_finished <= 1;
            writes_issued <= writes_issued + t_counter'(1);
        end

        else if ( (thread_state == STATE_FENCE_REQ) &&
                (!fiu.c1TxAlmFull) &&
                (!fence_req_finished) )
        begin
            fiu.c1Tx.hdr = cci_mpf_c1_genReqHdr(eREQ_WRFENCE,
                                              t_cci_clAddr'('x),
                                              t_cci_mdata'(instr_mdata),
                                              wr_params_fence_req);
            fiu.c1Tx.valid <= (thread_state == STATE_FENCE_REQ) &&
                              (!fiu.c1TxAlmFull) &&
                              (!fence_req_finished) ;
            fence_req_finished <= 1;
            writes_issued <= writes_issued + t_counter'(1);
        end

        else if ( (thread_state == STATE_WRITE_BACK) &&
                (!fiu.c1TxAlmFull) &&
                (!write_back_finished) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_write_back;
            fiu.c1Tx.valid <= (thread_state == STATE_WRITE_BACK) &&
                                (!fiu.c1TxAlmFull) &&
                              (!write_back_finished) ;
            write_back_finished <= 1;
            writes_issued <= writes_issued + t_counter'(1);
        end

        else if ( (thread_state == STATE_WRITE_VALID) &&
                (!fiu.c1TxAlmFull) &&
                (!write_valid_finished) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_write_valid;
            fiu.c1Tx.valid <= (thread_state == STATE_WRITE_VALID) &&
                                (!fiu.c1TxAlmFull) &&
                              (!write_valid_finished) ;
            write_valid_finished <= 1;
            writes_issued <= writes_issued + t_counter'(1);
        end

        else if ( (thread_state == STATE_FINISH) &&
                (!fiu.c1TxAlmFull) &&
                (!finish_finished) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_finished;
            fiu.c1Tx.valid <= (thread_state == STATE_FINISH) &&
                                (!fiu.c1TxAlmFull) &&
                              (!finish_finished) ;
            finish_finished <= 1;
        end

        else if ( (thread_state == STATE_FINAL_FENCE) &&
                (!fiu.c1TxAlmFull) &&
                (!final_fence_finished) )
        begin
            fiu.c1Tx.hdr = cci_mpf_c1_genReqHdr(eREQ_WRFENCE,
                                              t_cci_clAddr'('x),
                                              t_cci_mdata'(42),
                                              wr_params_final_fence);
            fiu.c1Tx.valid <= (thread_state == STATE_FINAL_FENCE) &&
                              (!fiu.c1TxAlmFull) &&
                              (!final_fence_finished) ;
            final_fence_finished <= 1;
        end

        else if ((r_vl0_enemy) &&
                 (!fiu.c1TxAlmFull) &&
                 (thread_state != STATE_IDLE) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_vl0;
            fiu.c1Tx.valid <= ((vl0_enemy) &&
                              (r_vl0_enemy) &&
                              (!fiu.c1TxAlmFull));
        end
        else if ((r_vh0_enemy) &&
                 (!fiu.c1TxAlmFull) &&
                 (thread_state != STATE_IDLE) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_vh0;
            fiu.c1Tx.valid <= ((vh0_enemy) &&
                              (r_vh0_enemy) &&
                              (!fiu.c1TxAlmFull));
        end
        else if ((r_vh1_enemy) &&
                 (!fiu.c1TxAlmFull) &&
                 (thread_state != STATE_IDLE) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_vh1;
            fiu.c1Tx.valid <= ((vh1_enemy) &&
                              (r_vh1_enemy) &&
                              (!fiu.c1TxAlmFull));
        end
        else
        begin
            fiu.c1Tx.valid <= 0;
        end

        if (thread_state != STATE_WRITE_REQ)
        begin
            write_req_finished <= 0;
        end
        if (thread_state != STATE_FENCE_REQ)
        begin
          fence_req_finished <= 0;
        end
        if (thread_state != STATE_FINAL_FENCE)
        begin
          final_fence_finished <= 0;
        end
        if (thread_state != STATE_WRITE_BACK)
        begin
            write_back_finished <= 0;
        end
        if (thread_state != STATE_WRITE_VALID)
        begin
            write_valid_finished <= 0;
        end
        if  (thread_state != STATE_FINISH)
        begin
            finish_finished <= 0;
        end

    end


    // Write and fence responses received at the right moment
    always_ff @(posedge clk)
    begin

        if ((reset) || (thread_state==STATE_NEW_EXPERIMENT))
        begin
            write_rsp_finished <= 0;
            fence_rsp_finished <= 0;
            final_fence_rsp_finished <= 0;
        end

        else if (cci_c1Rx_isWriteRsp(fiu.c1Rx))
        begin
            if ( (thread_state == STATE_WRITE_RSP) &&
                  (fiu.c1Rx.hdr.mdata == t_cci_mdata'(instr_mdata)) )
            begin
                write_rsp_finished <= 1;
            end
        end

        else if (fiu.c1Rx.rspValid)
        begin
            if ( (thread_state == STATE_FENCE_RSP) &&
                  (fiu.c1Rx.hdr.mdata == t_cci_mdata'(instr_mdata)) )
            begin
                fence_rsp_finished <= 1;
            end
            if ( (thread_state == STATE_FINAL_FENCE_RSP) &&
                  (fiu.c1Rx.hdr.mdata == t_cci_mdata'(42)) )
            begin
                final_fence_rsp_finished <= 1;
            end
        end
        else
        begin
            write_rsp_finished <= 0;
            fence_rsp_finished <= 0;
            final_fence_rsp_finished <= 0;
        end

    end


    // Count non-enemy responses  and check if experiment is valid
    always_ff @(posedge clk)
    begin
        if ((reset) || (thread_state==STATE_NEW_EXPERIMENT))
        begin
            write_valid_data <= 512'b1;
            writes_received <= t_counter'(0);
            reads_received <= t_counter'(0);
        end

        if (cci_c1Rx_isWriteRsp(fiu.c1Rx))
        begin
            if ( (fiu.c1Rx.hdr.mdata != t_cci_mdata'(20)) &&
                 (fiu.c1Rx.hdr.mdata != t_cci_mdata'(21)) &&
                 (fiu.c1Rx.hdr.mdata != t_cci_mdata'(22)) )
                 begin
                    writes_received <= writes_received + t_counter'(1);
                    // If the write response did not arrive at the right time
                    if ( (thread_state != STATE_WRITE_RSP) ||
                          (fiu.c1Rx.hdr.mdata != t_cci_mdata'(instr_mdata)) )
                    begin
                        write_valid_data <= 512'b0;
                    end
                 end
        end

        if (cci_c0Rx_isReadRsp(fiu.c0Rx))
        begin
            if ( (fiu.c0Rx.hdr.mdata != t_cci_mdata'(23)) &&
                 (fiu.c0Rx.hdr.mdata != t_cci_mdata'(24)) &&
                 (fiu.c0Rx.hdr.mdata != t_cci_mdata'(25)) )
            begin
                reads_received <= reads_received + t_counter'(1);

                // If the read response did not arrive at the right time
                if ( (thread_state != STATE_READ_RSP) ||
                     (fiu.c0Rx.hdr.mdata != t_cci_mdata'(instr_mdata)) )
                begin
                      write_valid_data <= 512'b0 ;
                end
            end
        end

        if ( (fiu.c1Rx.rspValid) && !(cci_c1Rx_isWriteRsp(fiu.c1Rx)) )
        begin
            if ( (fiu.c1Rx.hdr.mdata != t_cci_mdata'(20)) &&
                 (fiu.c1Rx.hdr.mdata != t_cci_mdata'(21)) &&
                 (fiu.c1Rx.hdr.mdata != t_cci_mdata'(22)) )
            begin
                writes_received <= writes_received + t_counter'(1);

                // If the fence did not arrive as expected
                if ( (thread_state != STATE_FENCE_RSP) ||
                      (fiu.c1Rx.hdr.mdata != t_cci_mdata'(instr_mdata)) )
                begin
                      write_valid_data <= 512'b0;
                end
            end
        end

    end


    /// ====================================
    ///
    ///    Read logic
    ///
    /// ====================================

    t_cci_mpf_ReqMemHdrParams rd_params_read_req;

    t_cci_mpf_ReqMemHdrParams rd_params_vl0;
    t_cci_mpf_ReqMemHdrParams rd_params_vh0;
    t_cci_mpf_ReqMemHdrParams rd_params_vh1;

    always_comb
    begin
        // Use virtual address
        rd_params_read_req = cci_mpf_defaultReqHdrParams(1);

        rd_params_vl0 = cci_mpf_defaultReqHdrParams(1);
        rd_params_vh0 = cci_mpf_defaultReqHdrParams(1);
        rd_params_vh1 = cci_mpf_defaultReqHdrParams(1);

        // Choose the channel
        rd_params_read_req.vc_sel = t_ccip_vc'(instr_channel);

        rd_params_vl0.vc_sel = eVC_VL0;
        rd_params_vh0.vc_sel = eVC_VH0;
        rd_params_vh1.vc_sel = eVC_VH1;
    end


    // Read request
    t_cci_mpf_c0_ReqMemHdr rd_hdr_read_req;

    t_cci_mpf_c0_ReqMemHdr rd_hdr_vl0;
    t_cci_mpf_c0_ReqMemHdr rd_hdr_vh0;
    t_cci_mpf_c0_ReqMemHdr rd_hdr_vh1;

    assign rd_hdr_read_req = cci_mpf_c0_genReqHdr( eREQ_RDLINE_I,
                                           instr_addr + exp_count,
                                           t_cci_mdata'(instr_mdata),
                                           rd_params_read_req);



    assign rd_hdr_vl0 = cci_mpf_c0_genReqHdr( eREQ_RDLINE_I,
                                             finish_addr + 1,
                                             t_cci_mdata'(23),
                                             rd_params_vl0);

    assign rd_hdr_vh0 = cci_mpf_c0_genReqHdr( eREQ_RDLINE_I,
                                             finish_addr + 2,
                                             t_cci_mdata'(24),
                                             rd_params_vh0);

    assign rd_hdr_vh1 = cci_mpf_c0_genReqHdr( eREQ_RDLINE_I,
                                             finish_addr + 3,
                                             t_cci_mdata'(25),
                                             rd_params_vh1);


    always_ff @(posedge clk)
    begin
        if (reset || thread_state == STATE_NEW_EXPERIMENT)
        begin
            fiu.c0Tx.valid <= 1'b0;
            read_req_finished <= 0;
            reads_issued <= t_counter'(0);
        end
        else if ((thread_state == STATE_READ_REQ) && (!fiu.c0TxAlmFull) && (!read_req_finished) )
        begin
            fiu.c0Tx <=  cci_mpf_genC0TxReadReq(rd_hdr_read_req,
                                               (!read_req_finished && !fiu.c0TxAlmFull));
            read_req_finished <= 1;
            reads_issued <= reads_issued + t_counter'(1);
        end
        else if ((thread_state != STATE_IDLE) && (!fiu.c0TxAlmFull) && r_vl0_enemy)
        begin
            fiu.c0Tx <=  cci_mpf_genC0TxReadReq(rd_hdr_vl0, !fiu.c0TxAlmFull);
        end
        else if ((thread_state != STATE_IDLE) && (!fiu.c0TxAlmFull) && r_vh0_enemy)
        begin
            fiu.c0Tx <=  cci_mpf_genC0TxReadReq(rd_hdr_vh0, !fiu.c0TxAlmFull);
        end
        else if ((thread_state != STATE_IDLE) && (!fiu.c0TxAlmFull) && r_vh1_enemy)
        begin
            fiu.c0Tx <=  cci_mpf_genC0TxReadReq(rd_hdr_vh1, !fiu.c0TxAlmFull);
        end
        else
        begin
            fiu.c0Tx.valid <= 1'b0;
        end

        // Reset signals when we go to next state
        if (thread_state != STATE_READ_REQ)
        begin
            read_req_finished <= 0;
        end
    end

    // Read rsp

    always_ff @(posedge clk)
    begin
        if (reset || thread_state == STATE_NEW_EXPERIMENT)
        begin
            read_rsp_finished <= 0;
            write_back_data <= 0;
        end
        else if ( cci_c0Rx_isReadRsp(fiu.c0Rx) &&
                (thread_state == STATE_READ_RSP) )
        begin
            if (fiu.c0Rx.hdr.mdata == t_cci_mdata'(instr_mdata))
            begin
                case(pc)
                0:
                begin
                  write_back_data[63:0] <= fiu.c0Rx.data[63:0];
                end
                1:
                begin
                  write_back_data[127:64] <= fiu.c0Rx.data[63:0];
                end
                2:
                begin
                  write_back_data[191:128] <= fiu.c0Rx.data[63:0];
                end
                3:
                begin
                  write_back_data[255:192] <= fiu.c0Rx.data[63:0];
                end
                4:
                begin
                  write_back_data[319:256] <= fiu.c0Rx.data[63:0];
                end
                5:
                begin
                  write_back_data[383:320] <= fiu.c0Rx.data[63:0];
                end
                6:
                begin
                  write_back_data[447:384] <= fiu.c0Rx.data[63:0];
                end
                7:
                begin
                  write_back_data[511:448] <= fiu.c0Rx.data[63:0];
                end
                endcase
                read_rsp_finished <= 1;
            end
        end
        // Reset signals when we go to next state
        if (thread_state != STATE_READ_RSP)
        begin
            read_rsp_finished<= 0;
        end
    end



    // =========================================================================
    //
    // Just for VERBOSE mode like in test_random
    //
    // =========================================================================

    logic c0Rx_is_read_rsp;

    always_ff @(posedge clk)
    begin
        c0Rx_is_read_rsp <= cci_c0Rx_isReadRsp(fiu.c0Rx);
        if (c0Rx_is_read_rsp)
        begin
            cnt_rd_rsp <= cnt_rd_rsp + t_counter'(1);
        end

        if (reset)
        begin
            cnt_rd_rsp <= t_counter'(0);
            c0Rx_is_read_rsp <= 1'b0;
        end
    end

    logic c1Rx_is_write_rsp;
    t_cci_clNum c1Rx_cl_num;

    always_ff @(posedge clk)
    begin
        c1Rx_is_write_rsp <= cci_c1Rx_isWriteRsp(fiu.c1Rx);
        c1Rx_cl_num <= fiu.c1Rx.hdr.cl_num;

        if (c1Rx_is_write_rsp)
        begin
            // Count beats so multi-line writes get credit for all data
            cnt_wr_rsp <= cnt_wr_rsp + t_counter'(1) + t_counter'(c1Rx_cl_num);
        end

        if (reset )
        begin
            cnt_wr_rsp <= t_counter'(0);
            c1Rx_is_write_rsp <= 1'b0;
        end
    end





    //
    // This AFU never handles MMIO reads.  MMIO is managed in the CSR module.
    //

    assign fiu.c2Tx.mmioRdValid = 1'b0;


endmodule // app_afu
