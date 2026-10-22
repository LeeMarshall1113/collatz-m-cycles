import Collatz.MCycle105Certs10

/-!
# Certificates of the listed shapes of `data105`, chunks 40..43
-/

set_option Elab.async false

namespace Collatz

theorem certs105_40 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_40 = true := by
  decide +kernel

theorem certs105_41 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_41 = true := by
  decide +kernel

theorem certs105_42 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_42 = true := by
  decide +kernel

theorem certs105_43 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_43 = true := by
  decide +kernel

end Collatz
