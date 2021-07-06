`include "cci_mpf_test_conf_default.vh"
`include "cci_mpf_if.vh"
`include "cci_test_csrs.vh"


// Generated from the AFU JSON file by afu_json_mgr
`include "afu_json_info.vh"


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
    t_ccip_clAddr queue_addr;
    t_ccip_clAddr back_addr;
    t_ccip_clAddr head_tail_addr;
    t_counter read_elements;
    t_counter head;
    t_counter tail;
    t_counter elements;
//    t_counter buff_size;
    logic [7:0] vl0_enemy;
    logic [7:0] vh0_enemy;
    logic [7:0] vh1_enemy;


    // CSR 1 triggers start
    logic start;

    always_ff @(posedge clk)
    begin

        if (csrs.cpu_wr_csrs[1].en)
        begin
            queue_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[1].data);
            $display(" Queue at VA 0x%x", csrs.cpu_wr_csrs[1].data );
        end

        if (csrs.cpu_wr_csrs[2].en)
        begin
            head_tail_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[2].data);
            $display("Head and tail at VA 0x%x", csrs.cpu_wr_csrs[2].data);
        end

        if (csrs.cpu_wr_csrs[3].en)
        begin
            back_addr <= byteAddrToClAddr(csrs.cpu_wr_csrs[3].data);
            $display("Back at VA 0x%x", csrs.cpu_wr_csrs[3].data);
        end
        if (csrs.cpu_wr_csrs[4].en)
        begin
            elements <= csrs.cpu_wr_csrs[4].data;
        end
        if (csrs.cpu_wr_csrs[5].en)
        begin
            vl0_enemy <= csrs.cpu_wr_csrs[5].data;
        end
        if (csrs.cpu_wr_csrs[6].en)
        begin
            vh0_enemy <= csrs.cpu_wr_csrs[6].data;
        end
        if (csrs.cpu_wr_csrs[7].en)
        begin
            vh1_enemy <= csrs.cpu_wr_csrs[7].data;
        end
    end

    logic [1:0] wrline_channel;
    logic [1:0] wrline_req_type;
    logic [1:0] rdline_channel;
    logic rdline_mode_s;
    logic fence_rsp;
    logic fence;
    logic wr_rsp_write_head;



    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            wrline_req_type <= 2'b0;
            rdline_mode_s <= 1'b0;
            fence_rsp <= 0;
            fence <= 0;
            wr_rsp_write_head <= 0;
        end
        else if (csrs.cpu_wr_csrs[0].en)
        begin
            { 
              wrline_channel,
              wrline_req_type,
              rdline_channel,
              rdline_mode_s,
              fence_rsp,
              fence,
              wr_rsp_write_head} <= csrs.cpu_wr_csrs[0].data;
        end

        start <= csrs.cpu_wr_csrs[0].en;
        if (start)
        begin
            $display(" I have %d elements", elements );
            $display(" VL0 enemy %d frequency", vl0_enemy );
            $display(" VH0 enemy %d frequency", vh0_enemy );
            $display(" VH1 enemy %d frequency", vh1_enemy );
            $display(" Wrline channel type %d", wrline_channel );
            $display(" Wrline request type %d", wrline_req_type );
            $display(" Rdline channel type %d", rdline_channel );
            $display(" Rdline request type %d", rdline_mode_s );
            $display(" Fence response %d", fence_rsp );
            $display(" Fence %d", fence );
            $display(" Write head response %d", wr_rsp_write_head );
        end
    end



    // =========================================================================
    //
    //   State machines
    //
    // =========================================================================

    typedef enum logic [3:0]
    {
        STATE_IDLE,
        STATE_READ_TAIL,
        STATE_READ_TAIL_RSP,
        STATE_DEQUEUE,
        STATE_DEQUEUE_RSP,
        STATE_WRITE_HEAD,
        STATE_WRITE_HEAD_RSP,
        STATE_FENCE,
        STATE_FENCE_RSP,
        STATE_SEND_BACK,
        STATE_WB,
        STATE_WB_RSP
    }
    t_state;
    t_state thread_state;

    logic rd_tail_sent;
    logic rd_tail_finished;
    logic rd_dequeue_sent;
    logic rd_dequeue_finished;
    logic wr_head_sent;
    logic wr_head_finished;
    logic wr_fence_sent;
    logic wr_fence_finished;
    logic wr_send_back_sent;
    logic wb_sent;
    logic wb_finished;


    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            thread_state <= STATE_IDLE;
        end
        else
        begin
            case (thread_state)
                STATE_IDLE:
                begin
                    if (start)
                    begin
                        thread_state <= STATE_READ_TAIL;
                    end
                end

                STATE_READ_TAIL:
                begin
                    if (rd_tail_sent)
                    begin
                        thread_state <= STATE_READ_TAIL_RSP;
                    end
                end

                STATE_READ_TAIL_RSP:
                begin
                    if (rd_tail_finished && (tail != head))
                    begin
                        thread_state <= STATE_DEQUEUE;
                    end
                    if (rd_tail_finished && (tail == head))
                    begin
                        thread_state <= STATE_READ_TAIL;
                    end
                end

                STATE_DEQUEUE:
                begin
                    if (rd_dequeue_sent)
                    begin
                        thread_state <= STATE_DEQUEUE_RSP;
                    end
                end

                STATE_DEQUEUE_RSP:
                begin
                    if (rd_dequeue_finished)
                    begin
                        thread_state <= STATE_WRITE_HEAD;
                    end
                end

                STATE_WRITE_HEAD:
                begin
                    if (wr_head_sent)
                    begin
                        if ((!fence) && (wr_rsp_write_head))
                        begin
                            thread_state <= STATE_WRITE_HEAD_RSP;
                        end
                        else if (fence)
                        begin
                            thread_state <= STATE_FENCE;
                        end
                        else if (!fence  && (!wr_rsp_write_head))
                        begin
                            thread_state <= STATE_SEND_BACK;
                        end
                    end
                end

                STATE_WRITE_HEAD_RSP:
                begin
                    if (wr_head_finished)
                    begin
                        thread_state <= STATE_SEND_BACK;
                    end
                end

                STATE_FENCE:
                begin
                    if (wr_fence_sent)
                    begin
                        if (!fence_rsp)
                        begin
                            thread_state <= STATE_SEND_BACK;
                        end
                        else if (fence_rsp)
                        begin
                            thread_state <= STATE_FENCE_RSP;
                        end
                    end
                end

                STATE_FENCE_RSP:
                begin
                    if (wr_fence_finished)
                    begin
                        thread_state <= STATE_SEND_BACK;
                    end
                end

                STATE_SEND_BACK:
                begin
                    if (wr_send_back_sent)
                    begin
                        if (read_elements == elements)
                        begin
                            thread_state <= STATE_WB;
                        end
                        if (read_elements < elements)
                        begin
                            thread_state <= STATE_READ_TAIL;
                        end
                    end
                end

                STATE_WB:
                begin
                    if (wb_sent)
                    begin
                        thread_state <= STATE_WB_RSP;
                    end
                end

                STATE_WB_RSP:
                begin
                    if (wb_finished)
                    begin
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
    t_cci_mpf_ReqMemHdrParams wr_params_head;
    t_cci_mpf_ReqMemHdrParams wr_params_wb;
    t_cci_mpf_ReqMemHdrParams wr_params_sb;

    t_cci_mpf_ReqMemHdrParams wr_params_vl0;
    t_cci_mpf_ReqMemHdrParams wr_params_vh0;
    t_cci_mpf_ReqMemHdrParams wr_params_vh1;

    t_cci_mpf_ReqMemHdrParams wrfence_params;


    always_comb
    begin
        // Address is virtual or not
        wr_params_head = cci_mpf_defaultReqHdrParams(1);
        wr_params_wb = cci_mpf_defaultReqHdrParams(1);
        wr_params_sb = cci_mpf_defaultReqHdrParams(1);

        wr_params_vl0 = cci_mpf_defaultReqHdrParams(1);
        wr_params_vh0 = cci_mpf_defaultReqHdrParams(1);
        wr_params_vh1 = cci_mpf_defaultReqHdrParams(1);

        wrfence_params = cci_mpf_defaultReqHdrParams(1);
        wrfence_params.vc_sel = eVC_VA;
        wrfence_params.sop = 1'b0;

        // Write channel
        wr_params_head.vc_sel = t_ccip_vc'(wrline_channel);
        wr_params_wb.vc_sel = t_ccip_vc'(wrline_channel);

        wr_params_vl0.vc_sel = eVC_VL0;
        wr_params_vh0.vc_sel = eVC_VH0;
        wr_params_vh1.vc_sel = eVC_VH1;

    end



    t_cci_mpf_c1_ReqMemHdr wr_hdr_head;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_wb;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_sb;


    t_cci_mpf_c1_ReqMemHdr wr_hdr_vl0;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_vh0;
    t_cci_mpf_c1_ReqMemHdr wr_hdr_vh1;


    assign wr_hdr_head = cci_mpf_c1_genReqHdr(t_cci_c1_req'(wrline_req_type),
                                          head_tail_addr,
                                          t_cci_mdata'(0),
                                          wr_params_head);

    assign wr_hdr_wb = cci_mpf_c1_genReqHdr(t_cci_c1_req'(wrline_req_type),
                                          head_tail_addr + 2,
                                          t_cci_mdata'(1),
                                          wr_params_wb);

    assign wr_hdr_sb = cci_mpf_c1_genReqHdr(t_cci_c1_req'(wrline_req_type),
                                          back_addr + read_elements - 1,
                                          t_cci_mdata'(1),
                                          wr_params_sb);


    assign wr_hdr_vl0 = cci_mpf_c1_genReqHdr(t_cci_c1_req'(wrline_req_type),
                                             head_tail_addr + 3,
                                             t_cci_mdata'(10),
                                             wr_params_vl0);

    assign wr_hdr_vh0 = cci_mpf_c1_genReqHdr(t_cci_c1_req'(wrline_req_type),
                                             head_tail_addr + 3,
                                             t_cci_mdata'(11),
                                             wr_params_vh0);

    assign wr_hdr_vh1 = cci_mpf_c1_genReqHdr(t_cci_c1_req'(wrline_req_type),
                                             head_tail_addr + 3,
                                             t_cci_mdata'(12),
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

    // Read response logic
    logic [63:0] value;

    // Data to send
    always_ff @(posedge clk)
    begin
        if (thread_state == STATE_WRITE_HEAD)
        begin
            fiu.c1Tx.data <= t_ccip_clData'({448'h1, head});
        end
        else if (thread_state == STATE_SEND_BACK)
        begin
            fiu.c1Tx.data <= t_ccip_clData'({448'h1, value});
        end
        else if (thread_state == STATE_WB)
        begin
            fiu.c1Tx.data <= t_ccip_clData'(512'h1);
        end
    end

    // Write request
    // This controls fiu.c1TX.hdr && fiu.c1Tx.valid

    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            fiu.c1Tx.valid <= 1'b0;
            wr_head_sent <= 0;
            wr_send_back_sent <= 0;
            wr_fence_sent <= 0;
            wb_sent <= 0;
        end
        else if ( (thread_state == STATE_WRITE_HEAD) &&
                (!fiu.c1TxAlmFull) &&
                (!wr_head_sent) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_head;
            fiu.c1Tx.valid <= (thread_state == STATE_WRITE_HEAD) &&
                              (!fiu.c1TxAlmFull) &&
                              (!wr_head_sent) ;
            wr_head_sent <= 1;
        end
        else if ( (thread_state == STATE_FENCE) &&
                (!fiu.c1TxAlmFull) &&
                (!wr_fence_sent) )
        begin
            fiu.c1Tx.hdr = cci_mpf_c1_genReqHdr(eREQ_WRFENCE,
                                              t_cci_clAddr'('x),
                                              t_cci_mdata'(5),
                                              wrfence_params);
            fiu.c1Tx.valid <= (thread_state == STATE_FENCE) &&
                              (!fiu.c1TxAlmFull) &&
                              (!wr_fence_sent) ;
            wr_fence_sent <= 1;
        end
        else if ( (thread_state == STATE_SEND_BACK) &&
                (!fiu.c1TxAlmFull) &&
                (!wr_send_back_sent) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_sb;
            fiu.c1Tx.valid <= (thread_state == STATE_SEND_BACK) &&
                              (!fiu.c1TxAlmFull) &&
                              (!wr_send_back_sent) ;
            wr_send_back_sent <= 1;
        end

        else if ( (thread_state == STATE_WB) &&
                  (!fiu.c1TxAlmFull) &&
                  (!wb_sent) )
        begin
            fiu.c1Tx.hdr <= wr_hdr_wb;
            fiu.c1Tx.valid <= (thread_state == STATE_WB) &&
                              (!fiu.c1TxAlmFull) &&
                              (!wb_sent);
            wb_sent <= 1;
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

        if (thread_state != STATE_WRITE_HEAD)
        begin
            wr_head_sent <= 0;
        end
        if (thread_state != STATE_SEND_BACK)
        begin
            wr_send_back_sent <= 0;
        end
        if (thread_state != STATE_FENCE)
        begin
            wr_fence_sent <= 0;
        end
        if  (thread_state != STATE_WB)
        begin
            wb_sent <= 0;
        end

    end



    // Write response

    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            wr_head_finished <= 0;
            wr_fence_finished <= 0;
            wb_finished <= 0;
        end
        else if ( (cci_c1Rx_isWriteRsp(fiu.c1Rx)) &&
            (thread_state == STATE_WRITE_HEAD_RSP) &&
            (fiu.c1Rx.hdr.mdata == t_cci_mdata'(0)) )
        begin
            wr_head_finished <= 1;
        end
        else if ( fiu.c1Rx.rspValid  &&
            (thread_state == STATE_FENCE_RSP) &&
            (fiu.c1Rx.hdr.mdata == t_cci_mdata'(5)) )
        begin
            wr_fence_finished <= 1;
        end
        else if ( (cci_c1Rx_isWriteRsp(fiu.c1Rx)) &&
            (thread_state == STATE_WB_RSP) &&
            (fiu.c1Rx.hdr.mdata == t_cci_mdata'(1)) )
        begin
            wb_finished <= 1;
        end
        else
        begin
            wr_head_finished <= 0;
            wr_fence_finished <= 0;
            wb_finished <= 0;
        end
    end


    /// ====================================
    ///
    ///    Read logic
    ///
    /// ====================================

    t_cci_mpf_ReqMemHdrParams rd_params_tail;
    t_cci_mpf_ReqMemHdrParams rd_params_dequeue;

    t_cci_mpf_ReqMemHdrParams rd_params_vl0;
    t_cci_mpf_ReqMemHdrParams rd_params_vh0;
    t_cci_mpf_ReqMemHdrParams rd_params_vh1;

    always_comb
    begin
        // Use virtual address
        rd_params_tail = cci_mpf_defaultReqHdrParams(1);
        rd_params_dequeue = cci_mpf_defaultReqHdrParams(1);

        rd_params_vl0 = cci_mpf_defaultReqHdrParams(1);
        rd_params_vh0 = cci_mpf_defaultReqHdrParams(1);
        rd_params_vh1 = cci_mpf_defaultReqHdrParams(1);

        // Choose the channel
        rd_params_tail.vc_sel = t_ccip_vc'(rdline_channel);
        rd_params_dequeue.vc_sel = t_ccip_vc'(rdline_channel);

        rd_params_vl0.vc_sel = eVC_VL0;
        rd_params_vh0.vc_sel = eVC_VH0;
        rd_params_vh1.vc_sel = eVC_VH1;
    end


    // Read request
    t_cci_mpf_c0_ReqMemHdr rd_hdr_tail;
    t_cci_mpf_c0_ReqMemHdr rd_hdr_dequeue;

    t_cci_mpf_c0_ReqMemHdr rd_hdr_vl0;
    t_cci_mpf_c0_ReqMemHdr rd_hdr_vh0;
    t_cci_mpf_c0_ReqMemHdr rd_hdr_vh1;

    assign rd_hdr_tail = cci_mpf_c0_genReqHdr( (rdline_mode_s ? eREQ_RDLINE_S : eREQ_RDLINE_I),
                                           head_tail_addr + 1,
                                           t_cci_mdata'(0),
                                           rd_params_tail);
    assign rd_hdr_dequeue = cci_mpf_c0_genReqHdr( (rdline_mode_s ? eREQ_RDLINE_S : eREQ_RDLINE_I),
                                           queue_addr + head,
                                           t_cci_mdata'(1),
                                           rd_params_dequeue);


    assign rd_hdr_vl0 = cci_mpf_c0_genReqHdr( (rdline_mode_s ? eREQ_RDLINE_S : eREQ_RDLINE_I),
                                             head_tail_addr + 3,
                                             t_cci_mdata'(10),
                                             rd_params_vl0);

    assign rd_hdr_vh0 = cci_mpf_c0_genReqHdr( (rdline_mode_s ? eREQ_RDLINE_S : eREQ_RDLINE_I),
                                             head_tail_addr + 3,
                                             t_cci_mdata'(11),
                                             rd_params_vh0);

    assign rd_hdr_vh1 = cci_mpf_c0_genReqHdr( (rdline_mode_s ? eREQ_RDLINE_S : eREQ_RDLINE_I),
                                             head_tail_addr + 3,
                                             t_cci_mdata'(12),
                                             rd_params_vh1);

    // Read send logic
    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            fiu.c0Tx.valid <= 1'b0;
            rd_tail_sent <= 0;
            rd_dequeue_sent <= 0;
        end
        else if ((thread_state == STATE_READ_TAIL) && (!fiu.c0TxAlmFull) && (!rd_tail_sent))
        begin
            fiu.c0Tx <=  cci_mpf_genC0TxReadReq(rd_hdr_tail,
                                               (!rd_tail_sent && !fiu.c0TxAlmFull));
            rd_tail_sent <= 1;
        end
        else if ((thread_state == STATE_DEQUEUE) && (!fiu.c0TxAlmFull) && (!rd_dequeue_sent))
        begin
            fiu.c0Tx <=  cci_mpf_genC0TxReadReq(rd_hdr_dequeue,
                                               (!rd_dequeue_sent && !fiu.c0TxAlmFull));
            rd_dequeue_sent <= 1;
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
        if (thread_state != STATE_READ_TAIL)
        begin
            rd_tail_sent <= 0;
        end
        if (thread_state != STATE_DEQUEUE)
        begin
            rd_dequeue_sent <= 0;
        end
    end


    always_ff @(posedge clk)
    begin
        if (reset)
        begin
            rd_tail_finished <= 0;
            rd_dequeue_finished <= 0;
            read_elements <= 0;
            tail <= 0;
            head <= 0;
        end
        else if ( cci_c0Rx_isReadRsp(fiu.c0Rx) &&
                (thread_state == STATE_READ_TAIL_RSP) )
        begin
            if (fiu.c0Rx.hdr.mdata == t_cci_mdata'(0))
            begin
                tail <= fiu.c0Rx.data[63:0];
                rd_tail_finished <= 1;
            end
        end
        else if ( cci_c0Rx_isReadRsp(fiu.c0Rx) &&
                (thread_state == STATE_DEQUEUE_RSP) )
        begin
            if (fiu.c0Rx.hdr.mdata == t_cci_mdata'(1))
            begin
                value <= fiu.c0Rx.data[63:0];
                rd_dequeue_finished <= 1;
                read_elements <= read_elements + 1;
                head <= (head + 1) % 32;
      //          $display("Value read %d ",fiu.c0Rx.data[63:0]);
            end
        end

        // Reset signals when we go to next state
        if (thread_state != STATE_READ_TAIL_RSP)
        begin
            rd_tail_finished <= 0;
        end
       if (thread_state != STATE_DEQUEUE_RSP)
        begin
            rd_dequeue_finished <= 0;
        end
    end




    //
    // Just for VERBOSE mode like in test_random
    //

    logic c0Rx_is_read_rsp;

    always_ff @(posedge clk)
    begin
        c0Rx_is_read_rsp <= cci_c0Rx_isReadRsp(fiu.c0Rx);
        if (c0Rx_is_read_rsp)
        begin
            cnt_rd_rsp <= cnt_rd_rsp + t_counter'(1);
        end

        if (reset || wb_finished)
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

        if (reset || wb_finished)
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
