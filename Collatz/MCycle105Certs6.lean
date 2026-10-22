import Collatz.MCycle105Certs5

/-!
# Certificates of the listed shapes of `data105`, chunks 20..23
-/

set_option Elab.async false

namespace Collatz

theorem certs105_20 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_20 = true := by
  decide +kernel

theorem certs105_21 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_21 = true := by
  decide +kernel

theorem certs105_22 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_22 = true := by
  decide +kernel

theorem certs105_23 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_23 = true := by
  decide +kernel

end Collatz
