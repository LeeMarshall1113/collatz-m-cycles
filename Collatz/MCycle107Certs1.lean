import Collatz.MCycle107Shapes
import Collatz.MCycleGrid103
import Collatz.MCycleGrid3_107

/-!
# Certificates of the listed shapes of `data107`, chunks 0..11
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs107_0 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_0 = true := by
  decide +kernel

theorem certs107_1 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_1 = true := by
  decide +kernel

theorem certs107_2 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_2 = true := by
  decide +kernel

theorem certs107_3 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_3 = true := by
  decide +kernel

theorem certs107_4 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_4 = true := by
  decide +kernel

theorem certs107_5 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_5 = true := by
  decide +kernel

theorem certs107_6 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_6 = true := by
  decide +kernel

theorem certs107_7 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_7 = true := by
  decide +kernel

theorem certs107_8 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_8 = true := by
  decide +kernel

theorem certs107_9 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_9 = true := by
  decide +kernel

theorem certs107_10 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_10 = true := by
  decide +kernel

theorem certs107_11 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107_11 = true := by
  decide +kernel

end Collatz
