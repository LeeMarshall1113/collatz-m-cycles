import Collatz.MCycle109Certs27

/-!
# Certificates of the listed shapes of `data109`, chunks 108..111
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_108 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_108 = true := by
  decide +kernel

theorem certs109_109 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_109 = true := by
  decide +kernel

theorem certs109_110 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_110 = true := by
  decide +kernel

theorem certs109_111 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_111 = true := by
  decide +kernel

end Collatz
