                                                                                                                                                                                                                                               2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   + y  y  , y y  - y y   - y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 11    9 12    11 12   7 8    7 10    8 10   4 6    4 12    6 12   2 3    2 12    3 12   1 3    1 6    3 6   1 2    1 4    2 4   5 6 10    5 6 11    5 10 11    6 10 11   4 5 9    4 5 10    4 9 10    5 9 10   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2           2    2   2         2   2         2   2   2               2         2
          AOTinIdeal => ideal (y  , y  , y y  , y  , y , y , y y , y , y , y y , y , y , y , y y , y y , y , y y , y , y y y  , y y y , y y y  y  )
                                12   11   9 11   10   9   8   7 8   7   6   4 6   5   4   3   2 3   1 3   2   1 2   1   5 6 10   4 5 9   4 5 10 11
          graph => {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {1, 4}, set {1, 5}, set {1, 6}, set {4, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 60T  + 160T  + 239T  + 188T  + 60T
          hyperplanes => {a - c, c - e, c - g, a - e, a - f, a - g, b - d, d - f, b - e, b - f, b - g, e - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_11-y_9*y_12+y_11*y_12, y_7*y_8-y_7*y_10-y_8*y_10, y_4*y_6-y_4*y_12+y_6*y_12, y_2*y_3-y_2*y_12+y_3*y_12, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_4-y_2*y_4, y_5*y_6*y_10-y_5*y_6*y_11-y_5*y_10*y_11+y_6*y_10*y_11, y_4*y_5*y_9-y_4*y_5*y_10-y_4*y_9*y_10+y_5*y_9*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}},{{y_12^2, y_11^2, y_9*y_11, y_10^2, y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_4*y_6, y_5^2, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_10, y_4*y_5*y_9, y_4*y_5*y_10*y_11}})
G = graph {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {1, 4}, set {1, 5}, set {1, 6}, set {4, 6}}
