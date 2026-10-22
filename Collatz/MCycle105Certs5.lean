import Collatz.MCycle105Certs4

/-!
# Certificates of the listed shapes of `data105`, chunks 16..19
-/

set_option Elab.async false

namespace Collatz

theorem certs105_16 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_16 = true := by
  decide +kernel

theorem certs105_17 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_17 = true := by
  decide +kernel

theorem certs105_18 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_18 = true := by
  decide +kernel

theorem certs105_19 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_19 = true := by
  decide +kernel

end Collatz
