module xif_monitor_cpu_issue #(
    string FILENAME = "cpu_issue_dump.txt"  // Output file name
)(
    input logic clk_i,                         // Clock signal
    isolde_cv_x_if.cpu_issue issue_if // Specific modport instance for monitoring
);

    // File handle
    integer fh;

    // Open the file during initialization
    initial begin
        fh = $fopen(FILENAME, "w");
        if (fh == 0) begin
            $error("ERROR: Could not open file: %s", FILENAME);
            $finish;
        end
    end

    // Close the file at the end of simulation
    final begin
        $fclose(fh);
    end

    // Monitor and log values from the modport
    always @(posedge clk_i) begin
        if (issue_if.issue_valid) begin
            $fwrite(fh, "[Time: %0t] issue_valid: %b, issue_ready: %b\n", $time, issue_if.issue_valid, issue_if.issue_ready);
            $fwrite(fh, "  instr: 0x%h\n", issue_if.issue_req.instr);
            $fwrite(fh, "  mode: %0b\n", issue_if.issue_req.mode);
            $fwrite(fh, "  id: %0d\n", issue_if.issue_req.id);
            for (int i = 0; i < issue_if.X_NUM_RS; i++) begin
                $fwrite(fh, "  rs[%0d]: 0x%h (valid: %b)\n", i, issue_if.issue_req.rs[i], issue_if.issue_req.rs_valid[i]);
            end
            $fwrite(fh, "  ecs: 0x%h (valid: %b)\n", issue_if.issue_req.ecs, issue_if.issue_req.ecs_valid);
        end
    end

endmodule
