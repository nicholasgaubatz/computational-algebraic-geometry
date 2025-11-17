                                                                                                                                                                          2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y   + y y  , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y   + y y y   - y y y  , y , y , y , y , y , y , y , y , y , y  , y  )}
                              7 8    7 9    8 9   5 6    5 11    6 11   4 6    4 8    6 8   1 3    1 5    3 5   1 2    1 4    2 4   2 3 8    2 3 11    2 8 11    3 8 11   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2         2   2               2   2   2         2         2
          AOTinIdeal => ideal (y  , y  , y , y , y y , y , y , y y , y y , y , y , y , y y , y , y y , y , y y y , y y y , y y y , y y y y , y y y y )
                                11   10   9   8   7 8   7   6   5 6   4 6   5   4   3   1 3   2   1 2   1   4 5 8   2 3 8   2 3 4   4 5 7 9   2 3 7 9
          graph => {set {0, 3}, set {3, 4}, set {3, 5}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 6}, set {2, 5}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 50T  + 119T  + 155T  + 104T  + 28T
          hyperplanes => {a - d, d - e, d - f, a - e, a - f, a - g, b - e, e - g, b - g, c - f, f - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_9-y_8*y_9, y_5*y_6-y_5*y_11+y_6*y_11, y_4*y_6-y_4*y_8+y_6*y_8, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_2*y_3*y_8-y_2*y_3*y_11+y_2*y_8*y_11-y_3*y_8*y_11, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5*y_6, y_4*y_6, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_4*y_5*y_8, y_2*y_3*y_8, y_2*y_3*y_4, y_4*y_5*y_7*y_9, y_2*y_3*y_7*y_9}})
G = graph {set {0, 3}, set {3, 4}, set {3, 5}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 6}, set {2, 5}, set {5, 6}}
