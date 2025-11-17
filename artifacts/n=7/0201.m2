                                                                      2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y )               }
                              2 3    2 6    3 6   1 3    1 5    3 5   1   2   3   4   5   6   7   8
                                2   2   2   2   2   2               2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y , y y , y , y , y y y )
                                8   7   6   5   4   3   2 3   1 3   2   1   1 2 5
          graph => {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 5}, set {3, 6}}
                                 2      3      4      5     6
          hSeries => 1 + 8T + 26T  + 44T  + 41T  + 20T  + 4T
          hyperplanes => {a - e, b - e, e - g, a - f, a - g, b - g, c - f, d - g}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_2*y_3-y_2*y_6-y_3*y_6, y_1*y_3-y_1*y_5-y_3*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_1*y_2*y_5}})
G = graph {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 5}, set {3, 6}}
