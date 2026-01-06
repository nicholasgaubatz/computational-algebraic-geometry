                                                                                                                                                                                                                                                                                    2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   - y  y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y y  - y y y y   + y y y y   - y y y y   - y y y y  , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 10    9 12    10 12   5 6    5 10    6 10   2 4    2 8    4 8   1 4    1 6    4 6   2 3    2 7    3 7   7 8 11    7 8 12    7 11 12    8 11 12   3 4 11    3 4 12    3 11 12    4 11 12   1 3 5 9    1 3 5 11    1 3 9 11    1 5 9 11    3 5 9 11   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2           2   2   2   2         2   2               2         2   2
          AOTinIdeal => ideal (y  , y  , y  , y y  , y , y , y , y , y y , y , y , y y , y y , y , y y , y , y , y y y  , y y y  , y y y , y y y , y y y y  , y y y y , y y y y , y y y y , y y y y  y  , y y y y y , y y y y y , y y y y y  y  )
                                12   11   10   9 10   9   8   7   6   5 6   5   4   2 4   1 4   3   2 3   2   1   7 8 11   3 4 11   3 4 7   1 2 6   1 3 6 11   1 3 5 9   1 2 5 8   1 3 6 7   1 3 5 10 11   1 2 5 7 9   1 3 5 7 8   1 2 5 7 10 11
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 61T  + 168T  + 263T  + 219T  + 74T
          hyperplanes => {a - d, b - d, d - f, d - g, a - e, a - g, b - f, b - g, c - e, e - g, c - f, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_12-y_10*y_12, y_5*y_6-y_5*y_10+y_6*y_10, y_2*y_4-y_2*y_8-y_4*y_8, y_1*y_4-y_1*y_6-y_4*y_6, y_2*y_3-y_2*y_7-y_3*y_7, y_7*y_8*y_11-y_7*y_8*y_12-y_7*y_11*y_12+y_8*y_11*y_12, y_3*y_4*y_11-y_3*y_4*y_12-y_3*y_11*y_12+y_4*y_11*y_12, y_1*y_3*y_5*y_9-y_1*y_3*y_5*y_11+y_1*y_3*y_9*y_11-y_1*y_5*y_9*y_11-y_3*y_5*y_9*y_11, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}, {-4}, {-5}, {-5}, {-5}, {-6}},{{y_12^2, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_2*y_4, y_1*y_4, y_3^2, y_2*y_3, y_2^2, y_1^2, y_7*y_8*y_11, y_3*y_4*y_11, y_3*y_4*y_7, y_1*y_2*y_6, y_1*y_3*y_6*y_11, y_1*y_3*y_5*y_9, y_1*y_2*y_5*y_8, y_1*y_3*y_6*y_7, y_1*y_3*y_5*y_10*y_11, y_1*y_2*y_5*y_7*y_9, y_1*y_3*y_5*y_7*y_8, y_1*y_2*y_5*y_7*y_10*y_11}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}}
