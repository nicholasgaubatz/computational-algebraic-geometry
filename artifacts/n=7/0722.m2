                                                                                                                                                                                                                                                        2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y  - y y y  + y y y , y y y y   - y y y y   + y y y  y   - y y y  y   - y y y  y  , y , y , y , y , y , y , y , y , y , y  , y  )}
                              4 6    4 8    6 8   2 3    2 8    3 8   1 3    1 6    3 6   1 2    1 4    2 4   5 6 10    5 6 11    5 10 11    6 10 11   4 5 7    4 5 9    4 7 9    5 7 9   7 8 9 10    7 8 9 11    7 8 10 11    7 9 10 11    8 9 10 11   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2   2   2         2   2   2               2         2
          AOTinIdeal => ideal (y  , y  , y , y , y , y , y y , y , y , y , y y , y y , y , y y , y , y y y  , y y y , y y y y  , y y y y  , y y y y )
                                11   10   9   8   7   6   4 6   5   4   3   2 3   1 3   2   1 2   1   5 6 10   4 5 7   7 8 9 10   4 5 8 10   5 6 7 8
          graph => {set {0, 3}, set {3, 4}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 51T  + 129T  + 188T  + 148T  + 48T
          hyperplanes => {a - d, d - e, d - g, a - e, a - f, a - g, b - e, e - g, b - f, c - f, c - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_6-y_4*y_8+y_6*y_8, y_2*y_3-y_2*y_8+y_3*y_8, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_4-y_2*y_4, y_5*y_6*y_10-y_5*y_6*y_11-y_5*y_10*y_11+y_6*y_10*y_11, y_4*y_5*y_7-y_4*y_5*y_9-y_4*y_7*y_9+y_5*y_7*y_9, y_7*y_8*y_9*y_10-y_7*y_8*y_9*y_11+y_7*y_8*y_10*y_11-y_7*y_9*y_10*y_11-y_8*y_9*y_10*y_11, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_4*y_6, y_5^2, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_10, y_4*y_5*y_7, y_7*y_8*y_9*y_10, y_4*y_5*y_8*y_10, y_5*y_6*y_7*y_8}})
G = graph {set {0, 3}, set {3, 4}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {2, 5}, set {2, 6}}
