import Collatz.MCycle105Certs2

/-!
# Certificates of the listed shapes of `data105`, chunks 8..11
-/

set_option Elab.async false

namespace Collatz

theorem certs105_8 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_8 = true := by
  decide +kernel

theorem certs105_9 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_9 = true := by
  decide +kernel

theorem certs105_10 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_10 = true := by
  decide +kernel

theorem certs105_11 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_11 = true := by
  decide +kernel

end Collatz
