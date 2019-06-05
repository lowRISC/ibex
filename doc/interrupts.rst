.. _interrupts:

Interrupts
==========

Ibex requires a separate event/interrupt controller outside of the core that performs masking and buffering of multiple interrupt requests.
Communication with this event/interrupt controller is established through the following external core interface:

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

When external interrupts are enabled, the core will serve interrupt requests.
An interrupt request is signaled with ``irq_i`` being high.
The interrupt ID is signaled by ``irq_id_i`` and determines the address offset in the interrupt vector table of the core (see :ref:`exceptions-interrupts`).

Once the interrupt processing is completed, the core asserts ``irq_ack_o`` for one clock cycle and signals the identifier that has been completed in ``irq_id_o``.

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
   
As the interrupt identifier is registered once it is handled, it is allowed that the interrupt identifier at the input changes.
This behavior can be used to handle interrupt priorities.
But as the core may already have started interrupt processing, it is necessary to check the acknowledged ID.
An example cycle is shown in :numref:`irq-processing-prio`.

.. wavedrom::
   :name: irq-processing-prio
   :caption: Interrupt processing with priorization. The processing of ``ID0`` has already started.

   { "signal": [
     { "name": "clk_i",     "wave": "p...", "period": 2 },
     { "name": "irq_i",     "wave": "01..|.1." },
     { "name": "irq_id_i",  "wave": "x=.=|...", "data": ["ID0", "ID1"] },
     { "name": "irq_ack_o", "wave": "0...|10." },
     { "name": "irq_id_id", "wave": "x...|=x.", "data": ["ID0"] }
     ]
   }	     
