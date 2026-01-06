                                                                                                                                                                                                                                                                                                                                                       2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y  y   - y y  y   - y y  y   + y  y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              2 4    2 10    4 10   1 4    1 7    4 7   2 3    2 9    3 9   1 3    1 6    3 6   8 10 11    8 10 12    8 11 12    10 11 12   5 7 11    5 7 12    5 11 12    7 11 12   6 7 9    6 7 10    6 9 10    7 9 10   5 7 8    5 7 10    5 8 10    7 8 10   5 6 8    5 6 9    5 8 9    6 8 9   1 2 5    1 2 8    1 5 8    2 5 8   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2    2   2   2   2   2   2               2               2   2
          AOTinIdeal => ideal (y  , y  , y  , y , y , y , y , y , y , y y , y y , y , y y , y y , y , y , y y  y  , y y y  , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y y  y  )
                                12   11   10   9   8   7   6   5   4   2 4   1 4   3   2 3   1 3   2   1   8 10 11   5 7 11   6 7 9   3 4 9   5 7 8   5 6 8   1 2 7   3 4 6   1 2 6   1 2 5   5 6 9 10 11
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {2, 4}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 62T  + 174T  + 276T  + 231T  + 78T
          hyperplanes => {a - d, b - d, d - f, d - g, a - e, a - f, a - g, b - e, b - f, b - g, c - e, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_2*y_4-y_2*y_10-y_4*y_10, y_1*y_4-y_1*y_7-y_4*y_7, y_2*y_3-y_2*y_9-y_3*y_9, y_1*y_3-y_1*y_6-y_3*y_6, y_8*y_10*y_11-y_8*y_10*y_12-y_8*y_11*y_12+y_10*y_11*y_12, y_5*y_7*y_11-y_5*y_7*y_12-y_5*y_11*y_12+y_7*y_11*y_12, y_6*y_7*y_9-y_6*y_7*y_10-y_6*y_9*y_10+y_7*y_9*y_10, y_5*y_7*y_8-y_5*y_7*y_10-y_5*y_8*y_10+y_7*y_8*y_10, y_5*y_6*y_8-y_5*y_6*y_9-y_5*y_8*y_9+y_6*y_8*y_9, y_1*y_2*y_5-y_1*y_2*y_8-y_1*y_5*y_8+y_2*y_5*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-5}},{{y_12^2, y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_2*y_4, y_1*y_4, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_8*y_10*y_11, y_5*y_7*y_11, y_6*y_7*y_9, y_3*y_4*y_9, y_5*y_7*y_8, y_5*y_6*y_8, y_1*y_2*y_7, y_3*y_4*y_6, y_1*y_2*y_6, y_1*y_2*y_5, y_5*y_6*y_9*y_10*y_11}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {2, 4}, set {2, 6}}
