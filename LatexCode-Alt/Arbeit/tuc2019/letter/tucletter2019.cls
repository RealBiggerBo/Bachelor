%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
% Briefklasse für das Corporate Design 2019 der TU Chemnitz                   %
% (c) Mario Haustein (mario.haustein@hrz.tu-chemnitz.de), 2013-2021           %
%                                                                             %
% Dieses Material steht unter der Creative-Commons-Lizenz Namensnennung -     %
% Keine Bearbeitungen 4.0 International. Um eine Kopie dieser Lizenz zu       %
% sehen, besuchen Sie http://creativecommons.org/licenses/by-nd/4.0/deed.de.  %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\ProvidesClass{tucletter2019}[2024/01/31]

% Logo der Kulturhauptstadt
\newif\iftuckhs\tuckhstrue
\newif\iftuckhscolor\tuckhscolortrue
\DeclareOption{chemnitz2025}{\tuckhstrue}
\DeclareOption{chemnitz2025color}{\tuckhstrue\tuckhscolortrue}
\DeclareOption{chemnitz2025green}{\tuckhstrue\tuckhscolorfalse}
\DeclareOption{nochemnitz2025}{\tuckhsfalse}

% Druck in S/W
\newif\iftucblack\tucblackfalse
\DeclareOption{black}{\tucblacktrue}

% Englische Bezeichner
\newif\iftucenglish\tucenglishfalse
\DeclareOption{eng}{\tucenglishtrue}

% Kopfzeile abschalten (für vorgedrucktes Briefpapier).
\newif\iftuc@head\tuc@headtrue
\DeclareOption{nohead}{\tuc@headfalse}

% Standard-Schriften verwenden.
\newif\iftuc@roboto\tuc@robototrue
\DeclareOption{latexfonts}{\tuc@robotofalse}

% Nicht auf linksbündig umschalten.
\newif\iftuc@flushleft\tuc@flushlefttrue
\DeclareOption{noflushleft}{\tuc@flushleftfalse}

% Umschaltung zwischen persönlichen Angaben und Strukturangaben
\newif\iftuc@myname\tuc@mynametrue
\newif\iftuc@myloc\tuc@mylocfalse
\newif\iftuc@myphone\tuc@myphonefalse
\newif\iftuc@myfax\tuc@myfaxfalse
\newif\iftuc@myemail\tuc@myemailfalse
\DeclareOption{usemyname}{\tuc@mynametrue}
\DeclareOption{usemyloc}{\tuc@myloctrue}
\DeclareOption{usemyphone}{\tuc@myphonetrue}
\DeclareOption{usemyfax}{\tuc@myfaxtrue}
\DeclareOption{usemyemail}{\tuc@myemailtrue}
\DeclareOption{usemycontact}{\tuc@myloctrue\tuc@myphonetrue\tuc@myfaxtrue\tuc@myemailtrue}
\DeclareOption{usedepname}{\tuc@mynamefalse}
\DeclareOption{usedeploc}{\tuc@mylocfalse}
\DeclareOption{usedepphone}{\tuc@myphonefalse}
\DeclareOption{usedepfax}{\tuc@myfaxfalse}
\DeclareOption{usedepemail}{\tuc@myemailfalse}
\DeclareOption{usedepcontact}{\tuc@mylocfalse\tuc@myphonefalse\tuc@myfaxfalse\tuc@myemailfalse}

% Keine Gesamtseitenanzahl angeben.
\newif\iftuc@totpages\tuc@totpagestrue
\DeclareOption{nototpages}{\tuc@totpagesfalse}

% Folgelogos ausschalten.
\newif\iftuc@contlogo\tuc@contlogotrue
\DeclareOption{nocontlogo}{\tuc@contlogofalse}

% Umsatzsteuer-ID anzeigen.
\newif\iftuc@taxid\tuc@taxidfalse
\DeclareOption{showtaxid}{\tuc@taxidtrue}


% Default-Werte aus tucletter2019.lco laden.
\PassOptionsToClass{tucletter2019}{scrlttr2}

% Per default einseitiges Layout
\PassOptionsToClass{oneside}{scrlttr2}

% Die restlichen Optionen an die Basisklasse weiterreichen.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{scrlttr2}}

% Optionen verarbeiten.
\ProcessOptions*\relax

% Ein einseitiges Layout erzwingen, wenn das Logo auf jedem Seitenkopf zu sehen
% sein soll,
\iftuc@contlogo
\PassOptionsToClass{oneside}{scrlttr2}
\fi

% Version der Klasse festlegen (wichtig für Koexistenz zu lco-Dateien der alten Klasse).
\gdef\tucletter@version{2019}

% Auf der KOMA-Script Briefklasse aufbauen.
\LoadClass[fontsize=11pt]{scrlttr2}
\AtBeginDocument{\KOMAoptions{paper=a4}}	% A4-Fehlermeldung unterdrücken


% footskip:   7mm
% headsep:    26.1mm = 45.0mm (Papierrand bis Oberkante Satzspiegel laut CI) -
%                      12.0mm (Rand bis zur Kopfzeile) -
%                      13.2pt (Höhe Kopfzeile)
%                    = 80.7pt
%                    = Höhe des Briefkopfes (wenn Logo auf Folgeseiten angezeigt wird)
% headsep:    13.2pt = Eine Zeile (wenn kein Logo auf Folgeseiten angezeigt wird)
% headheight: 13.2pt = Eine Zeile
\RequirePackage{etex}
\iftuc@contlogo
\RequirePackage[a4paper,includeheadfoot,inner=25mm,outer=20mm,top=12mm,bottom=10.6mm,footskip=7mm,headheight=13.2pt,headsep=80.7pt,nomarginpar]{geometry}
\else
\RequirePackage[a4paper,includeheadfoot,inner=25mm,outer=20mm,top=12mm,bottom=10.6mm,footskip=7mm,headheight=13.2pt,headsep=14.2pt,nomarginpar]{geometry}
\fi
\RequirePackage{graphicx}
\RequirePackage{xcolor}
\RequirePackage{calc}
\RequirePackage{xifthen}
\RequirePackage{fix-cm}			% Ein paar exotische Warnung vermeiden.
\RequirePackage{translations}
\iftuc@totpages\RequirePackage{lastpage}\fi


%
% Schrift
%

% Zunächst ein Paar KOMA-Fonts definieren.
\newkomafont{firstheadline}{\bfseries}
\newkomafont{nextheadline}{\mdseries}
\newkomafont{footline}{\relax}
\newkomafont{locfield}{\relax}
\newkomafont{enclseparator}{\relax}
\newkomafont{ccseparator}{\relax}

% Wenn gewünscht Roboto laden.
\iftuc@roboto
\RequirePackage[default,sfdefault]{roboto}
\setkomafont{firstheadline}{\robotomedium}
\setkomafont{nextheadline}{\robotoregular}
\setkomafont{footline}{\roboto}
\setkomafont{locfield}{\roboto}
\setkomafont{addressee}{\roboto}
\setkomafont{specialmail}{\roboto}
\setkomafont{backaddress}{\roboto}
\setkomafont{pagenumber}{\roboto}
\setkomafont{placeanddate}{\roboto}
\setkomafont{subject}{\roboto\bfseries}
\setkomafont{enclseparator}{\roboto\bfseries}
\setkomafont{ccseparator}{\roboto\bfseries}
\fi

\renewcommand*{\headfont}{}
\renewcommand*{\footfont}{}
\renewcommand*{\pnumfont}{\usekomafont{pagenumber}}


%
% Farbe
%
\iftucblack
  \definecolor{tuccolor}{RGB}{0,0,0}
  \definecolor{tuccolor}{cmyk}{0.0,0.0,0.0,1.0}
  \iftuckhs
    \def\tuc@logo{tuc2019/logo/tuckhs_black}
  \else
    \def\tuc@logo{tuc2019/logo/tuc_black}
  \fi
\else
  \definecolor{tuccolor}{RGB}{0,95,80}
  \definecolor{tuccolor}{cmyk}{1.0,0.34,0.69,0.30}
  \iftuckhs
    \iftuckhscolor
      \iftucenglish
        \def\tuc@logo{tuc2019/logo/tuckhseng_color}
      \else
        \def\tuc@logo{tuc2019/logo/tuckhs_color}
      \fi
    \else
      \iftucenglish
        \def\tuc@logo{tuc2019/logo/tuckhseng_green}
      \else
        \def\tuc@logo{tuc2019/logo/tuckhs_green}
      \fi
    \fi
  \else
    \def\tuc@logo{tuc2019/logo/tuc_green}
  \fi
\fi


%
% Laut CI kein Einzug beim Beginn eines neuen Absatzes. Absatzabstand
% entspricht einem Zeilenabstand. Weiterhin wird sichergestellt, dass am Ende
% jeder Zeile mindestens 1em Freiraum bleibt.
%
\setlength{\parindent}{0pt}
\setlength{\parskip}{\baselineskip}
\setlength{\parfillskip}{1em plus 1fil}


%
% Abmessungen des Adressfensters nach DIN
%
% Einzug oberer Rand:   50mm
% Einzug linker Rand:   20mm
% Einzug rechter Rand: 105mm
% Höhe:                 40mm
%
% Die Haus-CI vergrößert die Höhe auf 45mm und
% verkleinert den oberen Rand auf 48mm.
%

% Kopfzeile
\setplength{firstheadvpos}{12mm}
\setplength{firstheadhpos}{25mm}
\setplength{firstheadwidth}{165mm}	% 210mm - 25mm - 20mm

% Adressfenster
\setplength{toaddrhpos}{25mm}
\setplength{toaddrvpos}{48mm}
\setplength{toaddrwidth}{90mm}
\setplength{toaddrheight}{45mm}
\setplength{backaddrheight}{10pt}	% 1 Zeile: SG 8pt + 2pt zusätzlich Luft
\setplength{toaddrindent}{0pt}

% Fußzeile
\setplength{firstfootvpos}{268.4mm}	% 297mm - 10.6mm - 18mm
\setplength{firstfoothpos}{25mm}
\setplength{firstfootwidth}{165mm}	% 210mm - 25mm - 20mm

% Betreff und nicht vorhandene Geschäftszeile
\setplength{refvpos}{103mm}		% 48mm + 45mm + 10mm
\setplength{refhpos}{25mm}
\setplength{refwidth}{165mm}		% 210mm - 25mm - 20mm
\setplength{refaftervskip}{0pt}
\setplength{subjectbeforevskip}{0pt}
\setplength{subjectaftervskip}{13.2pt}

% Absenderergänzung
\setplength{lochpos}{20mm}
\setplength{locvpos}{48mm}
\setplength{locwidth}{65mm}
\setplength{locheight}{45mm}

% Unterschrift
\setplength{sigindent}{0pt}
\setplength{sigbeforevskip}{3\baselineskip}


%
% Die Geschäftszeile ausblenden.
%
\KOMAoptions{refline=nodate}
\removereffields


%
% Adressfenster
%

% Keine Linie bei Absenderangabe
\KOMAoptions{backaddress=plain}

% Absenderinformation wächst nach unten. Achtung, die Box ist 10pt hoch, aber
% nur 8pt (\f@size) davon sind nutzbar. Bei mehreren Zeilen läuft die Box also
% ins Empfängerfeld hinein. Die zusätzlichen 2pt schaffen im Endeffekt ca. 12pt
% Zeilenabstand zur ersten Empfängerzeile und richten die Grundlinie mit der
% ersten Zeile der Absenderergänzungen aus.
\setkomavar{backaddressseparator}{\usekomavar{tucseparator}}
\setkomavar{backaddress}{\raisebox{2pt}{\rule{0pt}{\f@size pt}\smash{\parbox[t]{\hsize}{%
\raggedright\def\\{\usekomavar{backaddressseparator}\@ogobble}\usekomavar{tucbackaddress}}}}}

% Schriftgröße Absenderinformation
\addtokomafont{backaddress}{\fontsize{8pt}{9.6pt}\selectfont}

% Schriftgröße Empfänger
\addtokomafont{addressee}{\fontsize{11pt}{13.2pt}\selectfont}


%
% Versandart (sollte aber nicht genutzt werden)
%

% Formatierung
\renewcommand*{\specialmail@format}[1]{#1}

% Schriftgröße
\addtokomafont{specialmail}{\fontsize{11pt}{13.2pt}\selectfont}


%
% Anlagen und Verteiler
%
% Das ist ein Dirty-Hack, der KOMA-Interna ausnutzt.
%
\AtBeginLetter{%
\let\@rgscr@enclseparator@name\scr@enclseparator@name%
\let\@rgscr@enclseparator@var\scr@enclseparator@var%
\let\@rgscr@ccseparator@name\scr@ccseparator@name%
\let\@rgscr@ccseparator@var\scr@ccseparator@var%
\def\scr@enclseparator@name{\usekomafont{enclseparator}\@rgscr@enclseparator@name}%
\def\scr@enclseparator@var{\usekomafont{enclseparator}\@rgscr@enclseparator@var}%
\def\scr@ccseparator@name{\usekomafont{ccseparator}\@rgscr@ccseparator@name}%
\def\scr@ccseparator@var{\usekomafont{ccseparator}\@rgscr@ccseparator@var}}


%
% Faltmarken bei vorgedrucktem Papier deaktivieren.
%
\iftuc@head\else
\KOMAoptions{foldmarks=off}
\fi

% Faltmarken sind farbig.
\addtokomafont{foldmark}{\color{tuccolor}}

% Da scrlttr2 nur Linien als Faltmarken vorsieht, verkaufen wir ein Rechteck als Punkt.
\setplength{foldmarkhpos}{3mm}
\setplength{foldmarkthickness}{0.8pt}
\setplength{bfoldmarklength}{0.8pt}
\setplength{lfoldmarklength}{0.8pt}
\setplength{mfoldmarklength}{0.8pt}
\setplength{pfoldmarklength}{0.8pt}
\setplength{tfoldmarklength}{0.8pt}


%
% Betreff
%
\KOMAoptions{subject=untitled}
\addtokomafont{subject}{\fontsize{11pt}{13.2pt}\selectfont}


%
% Numerische Datumsangaben
%
\KOMAoptions{numericaldate}


%
% Signum linksbündig setzen und Funktion ergänzen.
%
\let\raggedsignature\raggedright

% Signum ohne Bild
\newcommand{\makesignature}[2][]{\ifthenelse{\isempty{#1}}{#2}{#2\newline\fontsize{11pt}{13.2pt}\selectfont #1}}

% Signum mit Bild
\newcommand{\makesignaturefig}[3][]{%
\hbox to 0pt{\smash{\raisebox{\baselineskip}{\includegraphics[height=0.85\useplength{sigbeforevskip}]{#3}}}\hss}%
\makesignature[#1]{#2}}

% Etwas umständlich, da ein \usekomavar im optionalen Argument als nichtleer gewertet wird.
\AtBeginLetter{\Ifkomavarempty{signature}{\setkomavar{signature}{\Ifkomavarempty{mysignature}{\relax}{\Ifkomavarempty{myfunction}%
{\makesignature{\usekomavar{mysignature}}}{\makesignature[\usekomavar{myfunction}]{\usekomavar{mysignature}}}}}}{\relax}}


%
% Kontaktdaten
%
% Diese \ifkomvavarempty-Orgie ist ein dirty Hack, der sicherstellen soll,
% dass die Variablen für die Kontaktdaten richtig expandiert werden. Enthält
% eine KOMA-Variable einen \usekoma-Befehl, der zu nichts expandiert wird, wird
% die übergeordnete KOMA-Variable trotzdem als nichtleer angesehen. Dies würde zu
% einem falschen Vorrang führen.
%
% Dieses Konstrukt aus KOMA-Variablen dient dazu, den Vorrang zwischen
% persönlichen Angaben und Angaben der Struktureinheit zu realisieren.
% Es ist ebenfalls möglich die Standardformatierung im Zweifel auszuhebeln,
% z.B. wenn Telefonnummern anzugeben sind, die nicht ins Nummernschema der
% Universität passen (abweichende Vorwahl, etc.).
%
\AtBeginLetter{%
\Ifkomavarempty{showname}{\iftuc@myname%
\Ifkomavarempty{myname}{\relax}{\setkomavar{showname}[\usekomavar*{myname}]{\usekomavar{myname}}}\else%
\Ifkomavarempty{depname}{\relax}{\setkomavar{showname}[\usekomavar*{depname}]{\usekomavar{depname}}}\fi}{\relax}%
% Hinweis: Das Gebäude ist laut CI nicht vorgesehen. Wir nehmen es aus
%          Kompatibilitätsgründen dennoch auf. Ggf. kann es später entfallen.
\Ifkomavarempty{showloc}{\iftuc@myloc%
\Ifkomavarempty{myloc}{\relax}{\setkomavar{showloc}[\usekomavar*{myloc}]{\usekomavar{myloc}}}\else%
\Ifkomavarempty{deploc}{\relax}{\setkomavar{showloc}[\usekomavar*{deploc}]{\usekomavar{deploc}}}\fi}{\relax}%
\Ifkomavarempty{showroom}{\iftuc@myloc%
\Ifkomavarempty{myroom}{\relax}{\setkomavar{showroom}[\usekomavar*{myroom}]{\usekomavar{myroom}}}\else%
\Ifkomavarempty{deproom}{\relax}{\setkomavar{showroom}[\usekomavar*{deproom}]{\usekomavar{deproom}}}\fi}{\relax}%
\Ifkomavarempty{showphone}{\iftuc@myphone%
\Ifkomavarempty{myphone}{\relax}{\setkomavar{showphone}[\usekomavar*{myphone}]{\usekomavar{tucphoneprefix}-\usekomavar{myphone}}}\else%
\Ifkomavarempty{depphone}{\relax}{\setkomavar{showphone}[\usekomavar*{depphone}]{\usekomavar{tucphoneprefix}-\usekomavar{depphone}}}\fi}{\relax}%
\Ifkomavarempty{showfax}{\iftuc@myfax%
\Ifkomavarempty{myfax}{\relax}{\setkomavar{showfax}[\usekomavar*{myfax}]{\usekomavar{tucfaxprefix}-\usekomavar{myfax}}}\else%
\Ifkomavarempty{depfax}{\relax}{\setkomavar{showfax}[\usekomavar*{depfax}]{\usekomavar{tucfaxprefix}-\usekomavar{depfax}}}\fi}{\relax}%
\Ifkomavarempty{showemail}{\iftuc@myemail%
\Ifkomavarempty{myemail}{\relax}{\setkomavar{showemail}[\usekomavar*{myemail}]{\usekomavar{myemail}}}\else%
\Ifkomavarempty{depemail}{\relax}{\setkomavar{showemail}[\usekomavar*{depemail}]{\usekomavar{depemail}}}\fi}{\relax}%
\Ifkomavarempty{showurl}{%
\Ifkomavarempty{depurl}{\relax}{\setkomavar{showurl}[\usekomavar*{depurl}]{\usekomavar{depurl}}}}{\relax}}


%
% Kopf- und Fußzeilen für die Folgeseiten.
%
\pagestyle{myheadings}


%
% Briefkopf
%
\addtokomafont{firstheadline}{\fontsize{12pt}{19pt}\selectfont}
\addtokomafont{nextheadline}{\fontsize{12pt}{19pt}\selectfont}

\newcommand{\m@keheadline}[3]{\raisebox{#2}{\makebox{\hbox to #1{#3\hfill}}}}
\setkomavar{firsthead}{%
\newcommand{\firstheadline}{\usekomafont{firstheadline}}%
\newcommand{\nextheadline}{\usekomafont{nextheadline}}%
\setlength{\unitlength}{1mm}%
\iftuckhs
% Das Logo hat die Abmessungen 39.66 x 23.64mm. Die Höhe ist gleich dem regulären Logo.
\begin{picture}(165, 23.65)(0, -23.65)
\iftuc@head
\put(0, -23.65){\makebox(39.66, 23.65)[l]{\includegraphics[width=39.66mm]{\tuc@logo}\hspace*{10mm}}}%
\fi
% Die Linie hat eine Gesamtlänge von 25mm und damit einen kleinen Überstand nach oben und unten.
\put(49.66, -24.325){\makebox(0, 25.0)[t]{\hspace*{-0.375pt}\vrule width 0.75pt height 25.0mm}}
\put(59.66, -23.65){\m@keheadline{105mm}{57pt}{\firstheadline\usekomavar{tucheadline1}}}
\put(59.66, -23.65){\m@keheadline{105mm}{38pt}{\nextheadline\usekomavar{tucheadline2}}}
\put(59.66, -23.65){\m@keheadline{105mm}{19pt}{\nextheadline\usekomavar{tucheadline3}}}
\put(59.66, -23.65){\m@keheadline{105mm}{00pt}{\nextheadline\usekomavar{tucheadline4}}}
\end{picture}
\else
% Das Logo hat die Abmessungen 47mm x 23.65mm. Die Breite ist maßgeblich.
\begin{picture}(165, 23.65)(0, -23.65)
\iftuc@head
\put(0, -23.65){\makebox(47, 23.65)[l]{\includegraphics[width=47mm]{\tuc@logo}\hspace*{10mm}}}%
\fi
% Die Linie hat eine Gesamtlänge von 25mm und damit einen kleinen Überstand nach oben und unten.
\put(57, -24.325){\makebox(0, 25.0)[t]{\hspace*{-0.375pt}\vrule width 0.75pt height 25.0mm}}
\put(67, -23.65){\m@keheadline{98mm}{57pt}{\firstheadline\usekomavar{tucheadline1}}}
\put(67, -23.65){\m@keheadline{98mm}{38pt}{\nextheadline\usekomavar{tucheadline2}}}
\put(67, -23.65){\m@keheadline{98mm}{19pt}{\nextheadline\usekomavar{tucheadline3}}}
\put(67, -23.65){\m@keheadline{98mm}{00pt}{\nextheadline\usekomavar{tucheadline4}}}
\end{picture}
\fi
}


%
% Kopf der Folgeseiten
%
% - Das Logo ist 47mm breit.
% - Das Logo wird 13.2pt nach oben verschoben, da die Grundlinie der Kopfzeile
%   13.2pt unter dem 12mm-Rand des Satzspiegels liegt.
% - Da auf dem Briefkopf 25mm für die Kopfzeile freigehalten werden, wird das
%   Logo hier ebenfalls vertikal in einem 25mm-Rahmen zentriert.
%
\setkomavar{nexthead}{}
\iftuc@contlogo\iftuc@head
\iftuckhs
\setkomavar{nexthead}{\hsize=39.66mm\vbox to 0pt{\vskip -13.2pt\vbox to 25mm{\vfill{\includegraphics[width=36.66mm]{\tuc@logo}}\vfill}\vss}\hfill}
\else
\setkomavar{nexthead}{\hsize=47mm\vbox to 0pt{\vskip -13.2pt\vbox to 25mm{\vfill{\includegraphics[width=47mm]{\tuc@logo}}\vfill}\vss}\hfill}
\fi
\fi\fi


%
% Fußzeile der ersten Briefseite
%
% Das \if@tempswa-Konstrukt dient dazu leere Fußzeilen auszulassen.
%
% Mittels \removelastskip wird evt. überflüssiger vertikaler Zwischenraum
% getilgt, sollte ein Block ganz entfallen.
%
% Am Ende ist ein vertikaler Zwischenraum von 0pt erforderlich, damit
% \removelastskip wirkt.
%
% Die Fußzeile wird auf folgende Weise konstruiert_
%
% 1. Die Kontaktangaben werden gesetzt und in einer Box gespeichert.
% 2. Die Höhe dieser Box wird gemessen.
% 3. Die Logo-Box mit vorgegebener Breite und gemessener Höhe wird konstruiert.
% 4. Die gespeicherte Fußzeilenbox wird ausgegeben.
%
% 18mm = Höhe Fußzeile
% 57mm = Breite Logo-Box
% 98mm = Länge der Kopfzeilen = Länge der Fußzeilen
%
\addtokomafont{footline}{\fontsize{8pt}{9.6pt}\selectfont}

\newcommand{\m@kefootentry}[2]{%
\Ifkomavarempty{#1}{\relax}{\usekomavar*{#1}\Ifkomavarempty*{#1}{\relax}{#2}\usekomavar{#1}}}

\setkomavar{firstfoot}{%
\begin{minipage}[b][18mm][b]{\hsize}
\usekomafont{footline}%
\locbox{\footlines}
\savebox{\footlines}{%
\parbox[b]{98mm}{%
\raggedright%
\def\\{\usekomavar{tucseparator}\@ogobble}%
\Ifkomavarempty{visitaddress}{}{\par\m@kefootentry{visitaddress}{:~}}%
\Ifkomavarempty{fromaddress}{}{\par\m@kefootentry{fromaddress}{:~}}%
\removelastskip
\vskip 5.3pt%
\@tempswatrue%
\Ifkomavarempty{tucbankaccount}{\@tempswafalse}{}%
\Ifkomavarempty{tucbankcode}{\@tempswafalse}{}%
\Ifkomavarempty{tucbankaccountnr}{\@tempswafalse}{}%
\if@tempswa%
\par\m@kefootentry{tucbankaccount}{:~}%
\par\m@kefootentry{tucbankaccountnr}{:~}\\\m@kefootentry{tucbankcode}{:~}%
\iftuc@taxid\Ifkomavarempty{tuctaxid}{\relax}{\\\m@kefootentry{tuctaxid}{:~}}\fi%
\fi%
\removelastskip%
\vskip 0pt}}%
\setlength{\vsize}{\ht\footlines}
% Mindestgröße des Logos (4 Fußzeilen + Zwischenraum):
%   8pt + 3 * 9.4pt + 5.3pt = 41.5pt
\ifdim\vsize<41.5pt\setlength{\vsize}{41.5pt}\fi
\begin{minipage}[b][\vsize][c]{57mm}
\Ifkomavarempty{logo}{\m@kelogos}{\usekomavar{logo}}%
\end{minipage}%
\hfill%
\usebox{\footlines}%
\end{minipage}}


%
% Fußzeile der Folgeseiten
%
\AtBeginDocument{\ifcurrentbaselanguage{German}{\newcommand{\ofname}{von}}{\newcommand{\ofname}{of}}}

% Keine Verlinkung, wenn Hyperref geladen ist.
\newcommand{\m@kepage}{\pagename~\thepage\iftuc@totpages~\ofname~\pageref{LastPage}\fi}
\AtBeginDocument{%
  \@ifpackageloaded{hyperref}{%
    \renewcommand{\m@kepage}{\pagename~\thepage\iftuc@totpages~\ofname~\pageref*{LastPage}\fi}%
  }{}%
}
\setkomavar{nextfoot}{\if@twoside\Ifthispageodd{\hfill\m@kepage}{\m@kepage\hfill}\else\hfill\m@kepage\fi}


%
% Absenderergänzung
%
\addtokomafont{locfield}{\fontsize{8pt}{11pt}\selectfont}

\KOMAoptions{fromalign=off}

\newcommand{\m@kelocline}[2]{\par\hbox{\rule{0pt}{\f@size pt}%
\hbox to 20mm{#1\hfill}\parbox[t]{45mm}{\raggedright #2}}}

\newcommand{\m@kel@cline}[1]{%
\Ifkomavarempty{#1}{\relax}{\m@kelocline{%
\Ifkomavarempty*{#1}{\relax}{\usekomavar*{#1}:}}{\usekomavar{#1}}}}

\setkomavar{location}{%
\usekomafont{locfield}%
\hbox to 0pt{%			% Hack, da KOMA-Script nicht die volle location-Box ausnutzt (vlt. ein Bug?)
\begin{minipage}[t]{\hsize}
\begingroup
\@tempswafalse%
\m@kel@cline{myref}\Ifkomavarempty{myref}{\relax}{\@tempswatrue}%
\if@tempswa\vskip\baselineskip\fi%
\@tempswafalse%
\m@kel@cline{showname}\Ifkomavarempty{showname}{\relax}{\@tempswatrue}%
\m@kel@cline{showloc}\Ifkomavarempty{showloc}{\relax}{\@tempswatrue}%
\m@kel@cline{showroom}\Ifkomavarempty{showroom}{\relax}{\@tempswatrue}%
\m@kel@cline{showphone}\Ifkomavarempty{showphone}{\relax}{\@tempswatrue}%
\m@kel@cline{showfax}\Ifkomavarempty{showfax}{\relax}{\@tempswatrue}%
\m@kel@cline{showemail}\Ifkomavarempty{showemail}{\relax}{\@tempswatrue}%
\m@kel@cline{showurl}\Ifkomavarempty{showurl}{\relax}{\@tempswatrue}%
\if@tempswa\vskip\baselineskip\fi%
\@tempswafalse%
\newkomavar{dateplace}
\setkomavar{dateplace}{\Ifkomavarempty{place}{\relax}{\usekomavar{place}\usekomavar{placeseparator}}\usekomavar{date}}
\setkomavar*{dateplace}{\Ifkomavarempty{place}{\relax}{\Ifkomavarempty*{place}{\relax}{\usekomavar*{place},~}}\usekomavar*{date}}
\Ifkomavarempty{date}{\setkomavar{dateplace}[]{}}{\relax}
\Ifkomavarempty*{date}{\setkomavar*{dateplace}{}}{\relax}
\m@kel@cline{dateplace}\Ifkomavarempty{dateplace}{\relax}{\@tempswatrue}%
\endgroup
\end{minipage}\hss}}


%
% Logo-Container
%
% Die Logos sollen ein Maximum der zur Verfügung stehenden Fläche ausnutzen.
%
% Bei einem Logo wird das Logo durch \includegraphics so weit skaliert, dass
% sowohl Höhe als auch Breite eingehalten werden.
%
% Im Fall zweier Logos gibt es zwei Fälle zu betrachten.
%
% Fall 1: Beide Logos werden durch die Höhe des Containers begrenzt. Dann muss
%         zusätzlicher horizontaler Zwischenraum zwischen den Logos eingefügt
%         werden.
% Fall 2: Die Logos werden durch die Containerbreite begrenzt. Es soll laut CI
%         die genutzte Fläche maximiert werden. Dies führt u.U. aber dazu, dass
%         ein Logo sehr groß skaliert wird und das andere klein. Das "Optimum"
%         entspricht einem der folgenden Fälle:
%
%    x_1 = X - Y / r_2   x_2 =     Y / r_2   (Logo 2 hat volle Höhe)
%    x_1 =     Y / r_1   x_2 = X - Y / r_1   (Logo 1 hat volle Höhe)
%
%         Wobei die Variablen folgende Bedeutung haben:
%
%    r_1, r_2 ... Verhältnis von Höhe zu Breite der Logos
%    X, Y     ... Abmessungen des Logo-Containers
%    x_1, x_2 ... Breite von Logo 1 bzw. Logo 2
%
%
% Achtung: Wenn r_1 = r_2, dann führen beide Wahlmöglichkeiten für x_1 und x_2
%          zur selben Flächenausnutzung, aber zu vollkommen unterschiedlichen
%          Layouts. Für r_1 = r_2 = X / Y nimmt ein Logo den kompletten Platz
%          ein und das andere verschwindet.
%
% Aus diesem Grund ist es sinnvoller beide Logos so zu skalieren, dass sie die
% selbe Höhe einnehmen und den horizontalen Platz ausnutzen. Das ist allerdings
% genau der Fall, in dem die ausgenutze Fläche minimal wird. x_1 und x_2
% berechnen sich dann durch:
%
%    x_1 = r_1 / (r_1 + r_2) * X
%    x_2 = r_2 / (r_1 + r_2) * X
%
% Diese Variante sollte damit eher den Intentionen der CI-Autoren entsprechen
% und hat den Vorteil, dass bei richtiger Implementierung die obige
% Fallunterscheidung nicht mehr notwendig ist.
%

% Logo-Container füllen.
\newcommand{\m@kelogos}{\Ifkomavarempty{logo1}{\relax}{\Ifkomavarempty{logo2}{\m@kelogos@single}{\m@kelogos@double}}}

% Ein Logo
\newcommand{\m@kelogos@single}{\usekomavar[\edef\l@g@]{logo1}%
\includegraphics[height=\vsize,width=\hsize,keepaspectratio]{\l@g@}\hspace*{\fill}}

% Zwei Logos
\newcommand{\m@kelogos@double}{%
\begingroup%
\locbox{\logoi}%
\locbox{\logoii}%
\savebox{\logoi}{\usekomavar[\edef\l@g@]{logo1}\includegraphics{\l@g@}}%
\savebox{\logoii}{\usekomavar[\edef\l@g@]{logo2}\includegraphics{\l@g@}}%
\newlength{\l@g@scale}\setlength{\l@g@scale}{\hsize*\ratio{1pt}{1pt*\ratio{\ht\logoi}{\wd\logoi} + 1pt*\ratio{\ht\logoii}{\wd\logoii}}}%
\newlength{\l@g@iwidth}\setlength{\l@g@iwidth}{\l@g@scale*\ratio{\ht\logoii}{\wd\logoii}}%
\newlength{\l@g@iiwidth}\setlength{\l@g@iiwidth}{\l@g@scale*\ratio{\ht\logoi}{\wd\logoi}}%
\usekomavar[\edef\l@g@]{logo1}\(\vcenter{\hbox{\includegraphics[width=0.9\l@g@iwidth,height=\vsize,keepaspectratio]{\l@g@}}}\)%
\hspace*{\fill}%
\usekomavar[\edef\l@g@]{logo2}\(\vcenter{\hbox{\includegraphics[width=0.9\l@g@iiwidth,height=\vsize,keepaspectratio]{\l@g@}}}\)%
\endgroup}


%
% Ausrichtung des Textes.
%
\iftuc@flushleft
\AtBeginLetter{\raggedright}
\fi


\endinput
