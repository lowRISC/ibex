.. _interrupts:

Interrupts
==========

Interrupts are signaled via the external core interface:

+-------------------------+-----------+-----------------------------------------------+
| Signal                  | Direction | Description                                   |
+=========================+===========+===============================================+
| ``irq_i``               | in        | Interrupt event, level sensitive              |
+-------------------------+-----------+-----------------------------------------------+
| ``irq_id_i[4:0]``       | in        | Interrupt ID                                  |
+-------------------------+-----------+-----------------------------------------------+
| ``irq_ack_o``           | out       | Interrupt acknowledgement                     |
+-------------------------+-----------+-----------------------------------------------+
| ``irq_id_o[4:0]``       | out       | Interrupt acknowledgement ID                  |
+-------------------------+-----------+-----------------------------------------------+

When external interrupts are enabled, the core will serve interrupt requests. An interrupt is signaled as asserted high level at the ``irq_i`` signal. The interrupt ID determines the interrupt vector ID (0 to 31).

Once the interrupt processing is completed, the core will assert ``irq_ack_o`` for one clock cycle along with the identifier that has been completed.

.. important::

   The core may not start interrupt processing in the same cycle the level changes.
   
:numref:`irq-processing` shows the signal timing during a standard interrupt cycle.

.. wavedrom::
   :name: irq-processing
   :caption: Interrupt processing

   { "signal": [
     { "name": "clk_i",     "wave": "p...", "period": 2 },
     { "name": "irq_i",     "wave": "01..|.0." },
     { "name": "irq_id_i",  "wave": "x=..|.x.", "data": ["ID0"] },
     { "name": "irq_ack_o", "wave": "0...|10." },
     { "name": "irq_id_id", "wave": "x...|=x.", "data": ["ID0"] }
     ]
   }	     
   
As the interrupt identifier is registered once it is handled, it is allowed that the interrupt identifier at the input changes. This behavior can be used to handle interrupt priorities. But as the core may already have started interrupt processing, it is necessary to check the acknowledged ID. An example cycle is shown in :numref:`irq-processing-prio`.

.. wavedrom::
   :name: irq-processing-prio
   :caption: Typical interrupt processing with priorization on the interface. Here the processing of ``ID0`` has already started.

   { "signal": [
     { "name": "clk_i",     "wave": "p...", "period": 2 },
     { "name": "irq_i",     "wave": "01..|.1." },
     { "name": "irq_id_i",  "wave": "x=.=|...", "data": ["ID0", "ID1"] },
     { "name": "irq_ack_o", "wave": "0...|10." },
     { "name": "irq_id_id", "wave": "x...|=x.", "data": ["ID0"] }
     ]
   }	     
