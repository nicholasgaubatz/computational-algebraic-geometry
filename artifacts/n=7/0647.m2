                                                                                                                                                                                                                                    2   2   2   2   2   2   2   2   2   2    2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y  - y y   + y y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  , y  , y  )}
                              10 11    10 13    11 13   8 9    8 13    9 13   7 9    7 12    9 12   6 9    6 11    9 11   6 8    6 10    8 10   4 5    4 13    5 13   2 3    2 13    3 13   1 3    1 5    3 5   1 2    1 4    2 4   1   2   3   4   5   6   7   8   9   10   11   12   13
                                2    2    2            2    2                     2         2   2   2         2   2               2         2
          AOTinIdeal => ideal (y  , y  , y  , y  y  , y  , y , y y , y y , y y , y , y y , y , y , y , y y , y , y , y y , y y , y , y y , y , y y y  , y y y  , y y y  y  )
                                13   12   11   10 11   10   9   8 9   7 9   6 9   8   6 8   7   6   5   4 5   4   3   2 3   1 3   2   1 2   1   7 8 12   6 7 11   6 7 10 12
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 13T + 69T  + 191T  + 290T  + 228T  + 72T
          hyperplanes => {a - d, d - f, d - g, a - f, a - g, b - e, c - e, e - f, e - g, b - f, b - g, c - g, f - g}
          numVariables => 13
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_13]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10*y_11-y_10*y_13+y_11*y_13, y_8*y_9-y_8*y_13+y_9*y_13, y_7*y_9-y_7*y_12-y_9*y_12, y_6*y_9-y_6*y_11-y_9*y_11, y_6*y_8-y_6*y_10-y_8*y_10, y_4*y_5-y_4*y_13+y_5*y_13, y_2*y_3-y_2*y_13+y_3*y_13, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2, y_13^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}},{{y_13^2, y_12^2, y_11^2, y_10*y_11, y_10^2, y_9^2, y_8*y_9, y_7*y_9, y_6*y_9, y_8^2, y_6*y_8, y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_7*y_8*y_12, y_6*y_7*y_11, y_6*y_7*y_10*y_12}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}, set {5, 6}}
