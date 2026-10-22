import Collatz.MCycle105Certs8

/-!
# Certificates of the listed shapes of `data105`, chunks 32..35
-/

set_option Elab.async false

namespace Collatz

theorem certs105_32 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_32 = true := by
  decide +kernel

theorem certs105_33 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_33 = true := by
  decide +kernel

theorem certs105_34 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_34 = true := by
  decide +kernel

theorem certs105_35 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_35 = true := by
  decide +kernel

end Collatz
