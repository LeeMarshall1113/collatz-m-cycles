import Collatz.MCycle105Certs6

/-!
# Certificates of the listed shapes of `data105`, chunks 24..27
-/

set_option Elab.async false

namespace Collatz

theorem certs105_24 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_24 = true := by
  decide +kernel

theorem certs105_25 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_25 = true := by
  decide +kernel

theorem certs105_26 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_26 = true := by
  decide +kernel

theorem certs105_27 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_27 = true := by
  decide +kernel

end Collatz
