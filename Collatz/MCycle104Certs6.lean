import Collatz.MCycle104Certs5

/-!
# Certificates of the listed shapes of `data104`, chunks 20..23
-/

set_option Elab.async false

namespace Collatz

theorem certs104_20 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_20 = true := by
  decide +kernel

theorem certs104_21 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_21 = true := by
  decide +kernel

theorem certs104_22 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_22 = true := by
  decide +kernel

theorem certs104_23 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_23 = true := by
  decide +kernel

end Collatz
