# Dowód Thm 37 (Stirling, s. 52–54), krok po kroku

**Status:**
- Ta część nie jest sformalizowana. W Coqu `Thm37` występuje tylko jako hipoteza (`Small.v`). Udowodnione jest jedynie `Thm37 → rozstrzygalność`.
- W `stirling-formal.tex` (Thm. „small”) ten sam dowód jest rozpisany jako C1–C6 z lukami.

Poniżej zakładam prawdziwość wszystkiego, co jest przed Thm 37: gry (Thm 13), Fact 25–27, Prop. 28–32, partycji (Fact 33–35), unfoldingu (Def. 47, Fact 36). Kroki oznaczone **[rekonstrukcja]** to moja interpretacja miejsc, w których tekst jest tylko szkicem.

Oznaczenia:
- E: x w₁…w_k = u, rzędu 2p lub 2p+1, arności q;
- t: najmniejsze rozwiązanie (miara: rozmiar, potem liczba węzłów zmiennych);
- „etap” = stage z Def. 43, „grzebień” = comb z Def. 45.

---

## 0. Idea w trzech zdaniach

Najmniejsze rozwiązanie t może być głębokie tylko dlatego, że na jakiejś ścieżce powtarzają się te same zmienne (te same binders), a T1/T2 nie widzą tych powtórzeń, bo wiązania są „dalekie”. Unfolding przepisuje drzewo partycji tak, żeby wiązania stały się lokalne (powiększone grzebienie). Wtedy powtórzenia stają się α-równoważnymi kawałkami, które T2 wycina. Na końcu liczy się etapy, których T2 wyciąć nie może, i mnoży przez maksymalną głębokość powiększonego grzebienia.

## 1. Proste obserwacje o t (s. 52 dół – 53 góra)

**(O1) Poziomy i rozgałęzienie.**
- Każdy węzeł zmiennej ma poziom ≤ p (Lemat o poziomach).
- Rozgałęzienie węzła ≤ q.
- Długość wektora ȳ w λȳ ≤ q.

**(O2) Szufladki.** Jeśli jeden binder wiąże na jednej ścieżce (k+1)q węzłów, to co najmniej k z nich to węzły zagnieżdżone (embedded) z tą samą zmienną.
*Dowód.* Binder wiąże ≤ q zmiennych, więc któraś zmienna występuje ≥ k+1 razy. Wszystkie wystąpienia poza najwyższym są embedded (Def. 35). ∎

**(O3) Poziom p ⇒ end.** Następniki węzła poziomu p wiązałyby zmienne poziomu p+1, a takich nie ma.

**(O4) Liczba rozgrywek** = liczba gałęzi u ≤ |u|. ∀ wybiera gałąź tylko w węzłach stałych.

**(O5) T1 i T2 nie stosują się do t**, bo dałyby mniejsze rozwiązanie (Fact 30, Prop. 31). Wniosek: na każdej ścieżce t jest ≤ depth(u) stałych o arności > 0.
*Dowód.* Każdy taki węzeł jest odwiedzony (inaczej działa T1). Ścieżka od korzenia do najniższego z nich jest odwiedzana w jednej rozgrywce, przodkowie wcześniej (lemat `ancestors_visited`). Każde przejście przez stałą zmniejsza stan [r] w porządku podtermów u. ∎

## 2. Konstrukcja (a)–(c)

- (a) Zbuduj drzewo partycji dla wszystkich rozgrywek G(t,E): Def. 46, po jednym dla każdej rozgrywki, sklejone wspólnym początkiem.
- (b) Wykonaj unfolding wszędzie, gdzie się da (szczegóły w §3–4).
- (c) Wykonaj T1 i T2, dopóki się da.

Z wyniku odtwarza się term, sklejając (powiększone) grzebienie wzdłuż krawędzi drzewa. Teza: ten term jest rozwiązaniem i ma głębokość ≤ 4p²q^{2p−2}|u|.

**Separatory.** Wszystkie rozgrywki mają wspólny etap 1 i wspólny grzebień w etapie 2. Etap N jest *separatorem*, jeśli dwie różne rozgrywki mają te same grzebienie aż do N włącznie, a kończą N w różnych węzłach. Separatory są potrzebne, bo w drzewie partycji ten sam węzeł może mieć kilka krawędzi wchodzących z późniejszych etapów (różnych rozgrywek). Pod takim węzłem musi wisieć jeden i ten sam podterm. Separatory to dokładnie miejsca, w których rozgrywki się rozchodzą, więc trzeba je zachować.

## 3. Gdzie stosuje się unfolding

Startuje się od etapu N₁, który nie ma kontrybuujących potomków ze względu na wiązanie (descendants under binding). W szczególności nadaje się etap poziomu 1 albo etap zagnieżdżony. Powód: unfolding wymaga (Def. 47a), żeby N₁,…,N_k nie kontrybuowały.

## 4. Kluczowy argument szufladkowy (s. 53, środek)

Teza robocza: na żadnej ścieżce nie ma zbyt wielu węzłów jednego poziomu.

- Ustal k ≥ 0. Weź **najmniejsze** j takie, że jakaś ścieżka t zawiera ≥ (k+1)q^j węzłów poziomu j. **[rekonstrukcja]** Minimalność j daje, że węzłów poziomu < j jest na tej ścieżce mało. Zatem te (k+1)q^j węzłów poziomu j wiąże niewiele binderów: binder dla poziomu j to następnik węzła poziomu j−1. Z (O2) wynika, że ≥ k z nich to węzły embedded z tą samą zmienną.
- **Przypadek end.** Jeśli te k węzłów jest end, to k ≤ depth(u) (Prop. 32; w notatkach: ≤ depth(u)+1, luka 2).
- **Przypadek nie-end, k > q.** Wtedy któryś z nich, etap N₁, daje się rozwinąć w N₂ tak, że (N₁N₂) jest c-embedded (Def. 48). Powiększony grzebień jest α-równoważny powiększonemu grzebieniowi wyżej w drzewie partycji.
  **[rekonstrukcja]** Kandydatów na „kształt” (N₁N₂), czyli na to, który następnik grzebienia c₁ i która z ≤ q zmiennych przez niego wiązanych prowadzi do N₂, jest ≤ q. Przy > q powtórzeniach dwa mają ten sam kształt, a niższy jest c-embedded przez wyższy. Tekst tego nie mówi wprost.
- **Iteracja.** Jeśli k > q^l, to N₁ rozwija się w c-embedded (N₂…N_r) z r ≤ l+1. Każdy kolejny poziom zagnieżdżenia kosztuje czynnik q.
- **Założenie normalizujące.** W rozwinięciu (N₁…N_k) żaden N_j nie jest embedded z powodu wcześniejszego N_i (i < j). Inaczej rozwinięcie byłoby niepotrzebnie długie. Stąd:
  **głębokość powiększonego grzebienia ≤ 2pq^{p−1}**.
  Rachunek: węzeł poziomu 1 rozwija się w ≤ q węzłów poziomu 2, te razem w ≤ q² poziomu 3, i tak dalej. Daje to 1 + q + … + q^{p−1} ≤ p·q^{p−1} warstw. Czynnik 2 bierze się stąd, że każda warstwa to węzeł głowy plus węzeł λ.

Sens tego kroku: po wyczerpującym unfoldingu każde „długie” powtórzenie na ścieżce zamienia się w powiększony grzebień, który jest c-embedded, więc jego ścieżka od korzenia do liścia jest redundantną end path. Na nią działa T2 (krok (c)).

## 5. Co zachowuje unfolding

- Etap, który kontrybuował, nadal kontrybuuje.
- Nowy, rozwinięty etap nigdy nie kontrybuuje (Fact 36).
- Rozgrywka rozwiniętego etapu (N₁…N_k) startuje w korzeniu c₁ i kończy się w liściu n′ grzebienia (c₁…c_k). Zatem T2 stosuje się do niego, gdy ścieżka od korzenia c₁ do n′ jest redundantną end path.

## 6. Liczenie (s. 53 dół – 54 góra)

Liczymy etapy na ścieżce wynikowego termu, których T2 **nie** usuwa.

1. **Etapy kontrybuujące:** ≤ |u| łącznie (Cor. „contrib-stages”).
2. **Późniejsze etapy nie-embedded**, startujące od potomka (ze względu na wiązanie) korzenia grzebienia kontrybuującego: ≤ pq^{p−1} na jeden grzebień kontrybuujący. **[rekonstrukcja]** Potomkowie ze względu na wiązanie tworzą drzewo poziomów 1..p o rozgałęzieniu ≤ q. Na jednej ścieżce węzeł nie-embedded to pierwsze wystąpienie danej zmiennej danego bindera. Daje to ≤ q + q² + … ≤ p·q^{p−1}. W pracy nie ma tego argumentu.
3. **Separatory:** ≤ pq^{p−1}|u|, czyli nie więcej niż etapów z punktów 1–2. Argumentu też nie ma.

Wszystkie pozostałe etapy leżą w c-embedded powiększonych grzebieniach i T2 je usuwa. Na ścieżce zostaje zatem ≤ 2pq^{p−1}|u| etapów (z zapasem). Każdy wnosi (powiększony) grzebień głębokości ≤ 2pq^{p−1}. Iloczyn:

  2pq^{p−1}|u| · 2pq^{p−1} = **4p²q^{2p−2}|u|**.

Dla rzędu 5 (p = 2) daje to 16q²|u|. Dla przykładu 12 (q = 2, |u| = 2) wychodzi 128, jak w pracy.

## 7. Gdzie ten dowód jest cienki

| # | Miejsce | Co brakuje |
|---|---------|------------|
| a | §2 (b) | Że wynik unfoldingu jest termem i rozwiązaniem (luka 4). Dla głów nieliniowych powiększony grzebień nie jest drzewem: `order5-unfolding.md` §3. |
| b | §4 | Dlaczego k > q daje c-embedded (N₁N₂). To szufladki po „kształtach”, ale nie jest to napisane. |
| c | §4 | Minimalność j w argumencie (k+1)q^j: na ścieżce węzły poziomu j mogą być wiązane przez różne bindery. |
| d | §2 | Terminacja przeplotu „unfolding zwiększa, T1/T2 zmniejszają” (luka 5(i)). |
| e | §6.2, §6.3 | Ograniczenia pq^{p−1} oraz pq^{p−1}|u| dla separatorów: podane bez dowodu. |
| f | §6 | Że T2 stosuje się do *wszystkich* pozostałych etapów. Redundancja (Def. 41) dotyczy wszystkich rozgrywek naraz, a drzewo partycji jest per rozgrywka. |
| g | §6 | Arytmetyka sumy etapów jest zgrubna; wynik i tak jest poprawny co do rzędu wielkości. |

Punkty a, d, e i f to istota luk 4–5 z `stirling-formal.tex`.
