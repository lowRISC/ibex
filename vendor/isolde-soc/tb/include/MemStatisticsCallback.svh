`ifndef MEM_STATISTICS_SVH
`define MEM_STATISTICS_SVH

virtual class MemStatisticsCallback;
  pure virtual function int instMemWrites();
  pure virtual function int instrMemReads();
  pure virtual function int dataMemWrites();
  pure virtual function int dataMemReads();
  pure virtual function int stackMemWrites();
  pure virtual function int stackMemReads();
  pure virtual function int instrMemLatency();
      /**
  ** user defined string, avoid spaces
  **/
  pure virtual function string strInfo();
endclass

`endif  // MEM_STATISTICS_SVH
