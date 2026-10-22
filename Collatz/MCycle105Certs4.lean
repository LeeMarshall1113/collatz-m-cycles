import Collatz.MCycle105Certs3

/-!
# Certificates of the listed shapes of `data105`, chunks 12..15
-/

set_option Elab.async false

namespace Collatz

theorem certs105_12 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_12 = true := by
  decide +kernel

theorem certs105_13 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_13 = true := by
  decide +kernel

theorem certs105_14 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_14 = true := by
  decide +kernel

theorem certs105_15 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_15 = true := by
  decide +kernel

end Collatz
