import Collatz.MCycle109Certs11

/-!
# Certificates of the listed shapes of `data109`, chunks 44..47
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_44 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_44 = true := by
  decide +kernel

theorem certs109_45 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_45 = true := by
  decide +kernel

theorem certs109_46 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_46 = true := by
  decide +kernel

theorem certs109_47 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_47 = true := by
  decide +kernel

end Collatz
