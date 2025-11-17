                                                                      2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  - y y , y , y , y , y , y , y , y , y )               }
                              3 4    3 7    4 7   1 2    1 4    2 4   1   2   3   4   5   6   7   8
                                2   2   2   2   2         2   2         2
          AOTinIdeal => ideal (y , y , y , y , y , y y , y , y , y y , y )
                                8   7   6   5   4   3 4   3   2   1 2   1
          graph => {set {0, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 5}, set {5, 6}, set {3, 6}}
                                 2      3      4      5     6
          hSeries => 1 + 8T + 26T  + 44T  + 41T  + 20T  + 4T
          hyperplanes => {a - e, e - g, a - f, a - g, b - f, c - f, f - g, d - g}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_3*y_4-y_3*y_7+y_4*y_7, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3*y_4, y_3^2, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 5}, set {5, 6}, set {3, 6}}
