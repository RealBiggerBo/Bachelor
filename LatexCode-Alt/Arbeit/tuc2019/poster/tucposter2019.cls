%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
% Poster-Template für das Corporate Design 2019 der TU Chemnitz               %
% (c) Mario Haustein (mario.haustein@hrz.tu-chemnitz.de), 2014-2020           %
%                                                                             %
% Dieses Material steht unter der Creative-Commons-Lizenz Namensnennung -     %
% Weitergabe unter gleichen Bedingungen 4.0 International. Um eine Kopie      %
% dieser Lizenz zu sehen, besuchen Sie                                        %
% http://creativecommons.org/licenses/by-sa/4.0/deed.de.                      %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{tucposter2019}[2024/07/29]

\RequirePackage{etex}
\RequirePackage{xkeyval}
\RequirePackage{fp}

%
% Nach CI definierte Abmessungen festlegen.
%

% Poster A0
\expandafter\def\csname tucp@ster@tpl@a0\endcsname{
  \edef\tucp@ster@scale{4}
  \edef\tucp@ster@paperwidth{841mm}
  \edef\tucp@ster@paperheight{1189mm}
  \edef\tucp@ster@lmargin{43.4mm}
  \edef\tucp@ster@rmargin{43.4mm}
  \edef\tucp@ster@headpreskip@simple{43.4mm}
  \edef\tucp@ster@headpreskip@fancy{43.4mm}
  \edef\tucp@ster@headpostskip@simple{43.4mm}
  \edef\tucp@ster@headpostskip@fancy{86.8mm}
  \edef\tucp@ster@headlogosep{43.4mm}
  \edef\tucp@ster@headlogowidth{200mm}
  \edef\tucp@ster@headrule{4pt}
  \edef\tucp@ster@headnormalsize{66}
  \edef\tucp@ster@footheight@default{84.8mm}
  % Logo-Höhe: 60.5mm
  % Logo-Abstand: 0.5 * (Höhe Fußzeile - Logo-Höhe)
  \edef\tucp@ster@footmargin@default{12.15mm}
  \edef\tucp@ster@footrule@default{4pt}
  \edef\tucp@ster@footnormalsize{40}
  \edef\tucp@ster@fancytitle@size{75pt}
  \edef\tucp@ster@fancytitle@skip{92pt}
}

\expandafter\def\csname tucp@ster@tpl@a0l\endcsname{
  \csname tucp@ster@tpl@a0\endcsname
  \edef\tucp@ster@paperwidth{1189mm}
  \edef\tucp@ster@paperheight{841mm}
}

% Poster A1
\expandafter\def\csname tucp@ster@tpl@a1\endcsname{
  \edef\tucp@ster@scale{2.8284}
  \edef\tucp@ster@paperwidth{594mm}
  \edef\tucp@ster@paperheight{841mm}
  \edef\tucp@ster@lmargin{30.7mm}
  \edef\tucp@ster@rmargin{30.7mm}
  \edef\tucp@ster@headpreskip@simple{30.7mm}
  \edef\tucp@ster@headpreskip@fancy{30.7mm}
  \edef\tucp@ster@headpostskip@simple{30.7mm}
  \edef\tucp@ster@headpostskip@fancy{61.4mm}
  \edef\tucp@ster@headlogosep{30.7mm}
  \edef\tucp@ster@headlogowidth{141.5mm}
  \edef\tucp@ster@headrule{2.8pt}
  \edef\tucp@ster@headnormalsize{46.7}
  \edef\tucp@ster@footheight@default{61.4mm}
  \edef\tucp@ster@footmargin@default{8.59mm}
  \edef\tucp@ster@footrule@default{2.8pt}
  \edef\tucp@ster@footnormalsize{28.3}
  \edef\tucp@ster@fancytitle@size{53pt}
  \edef\tucp@ster@fancytitle@skip{65pt}
}

\expandafter\def\csname tucp@ster@tpl@a1l\endcsname{
  \csname tucp@ster@tpl@a1\endcsname
  \edef\tucp@ster@paperwidth{841mm}
  \edef\tucp@ster@paperheight{594mm}
}

% Poster A2
\expandafter\def\csname tucp@ster@tpl@a2\endcsname{
  \edef\tucp@ster@scale{2}
  \edef\tucp@ster@paperwidth{420mm}
  \edef\tucp@ster@paperheight{594mm}
  \edef\tucp@ster@lmargin{21.7mm}
  \edef\tucp@ster@rmargin{21.7mm}
  \edef\tucp@ster@headpreskip@simple{21.7mm}
  \edef\tucp@ster@headpreskip@fancy{21.7mm}
  \edef\tucp@ster@headpostskip@simple{21.7mm}
  \edef\tucp@ster@headpostskip@fancy{43.4mm}
  \edef\tucp@ster@headlogosep{21.7mm}
  \edef\tucp@ster@headlogowidth{100mm}
  \edef\tucp@ster@headrule{2pt}
  \edef\tucp@ster@headnormalsize{33}
  \edef\tucp@ster@footheight@default{43.4mm}
  \edef\tucp@ster@footmargin@default{6.07mm}
  \edef\tucp@ster@footrule@default{2pt}
  \edef\tucp@ster@footnormalsize{20}
  \edef\tucp@ster@fancytitle@size{37pt}
  \edef\tucp@ster@fancytitle@skip{46pt}
}

\expandafter\def\csname tucp@ster@tpl@a2l\endcsname{
  \csname tucp@ster@tpl@a2\endcsname
  \edef\tucp@ster@paperwidth{594mm}
  \edef\tucp@ster@paperheight{420mm}
}

% Poster A3
\expandafter\def\csname tucp@ster@tpl@a3\endcsname{
  \edef\tucp@ster@scale{1.4142}
  \edef\tucp@ster@paperwidth{297mm}
  \edef\tucp@ster@paperheight{420mm}
  \edef\tucp@ster@lmargin{15.3mm}
  \edef\tucp@ster@rmargin{15.3mm}
  \edef\tucp@ster@headpreskip@simple{15.3mm}
  \edef\tucp@ster@headpreskip@fancy{15.3mm}
  \edef\tucp@ster@headpostskip@simple{15.3mm}
  \edef\tucp@ster@headpostskip@fancy{30.7mm}
  \edef\tucp@ster@headlogosep{15.3mm}
  \edef\tucp@ster@headlogowidth{70.5mm}
  \edef\tucp@ster@headrule{1.4pt}
  \edef\tucp@ster@headnormalsize{23.3}
  \edef\tucp@ster@footheight@default{30.7mm}
  \edef\tucp@ster@footmargin@default{4.30mm}
  \edef\tucp@ster@footrule@default{1.4pt}
  \edef\tucp@ster@footnormalsize{14.1}
  \edef\tucp@ster@fancytitle@size{26.5pt}
  \edef\tucp@ster@fancytitle@skip{32.5pt}
}

\expandafter\def\csname tucp@ster@tpl@a3l\endcsname{
  \csname tucp@ster@tpl@a3\endcsname
  \edef\tucp@ster@paperwidth{420mm}
  \edef\tucp@ster@paperheight{297mm}
}

% Poster A4
\expandafter\def\csname tucp@ster@tpl@a4\endcsname{
  \edef\tucp@ster@scale{1}
  \edef\tucp@ster@paperwidth{210mm}
  \edef\tucp@ster@paperheight{297mm}
  \edef\tucp@ster@lmargin{10.85mm}
  \edef\tucp@ster@rmargin{10.85mm}
  \edef\tucp@ster@headpreskip@simple{10.85mm}
  \edef\tucp@ster@headpreskip@fancy{10.85mm}
  \edef\tucp@ster@headpostskip@simple{10.85mm}
  \edef\tucp@ster@headpostskip@fancy{21.7mm}
  \edef\tucp@ster@headlogosep{10.85mm}
  \edef\tucp@ster@headlogowidth{50mm}
  \edef\tucp@ster@headrule{1pt}
  \edef\tucp@ster@headnormalsize{16}
  \edef\tucp@ster@footheight@default{21.2mm}
  \edef\tucp@ster@footmargin@default{3.0375mm}
  \edef\tucp@ster@footrule@default{1pt}
  \edef\tucp@ster@footnormalsize{10}
  \edef\tucp@ster@fancytitle@size{19pt}
  \edef\tucp@ster@fancytitle@skip{23pt}
}

\expandafter\def\csname tucp@ster@tpl@a4l\endcsname{
  \csname tucp@ster@tpl@a4\endcsname
  \edef\tucp@ster@paperwidth{297mm}
  \edef\tucp@ster@paperheight{210mm}
}

% Wissenschaftliches Poster für Octanorm-Aufsteller
\def\tucp@ster@tpl@octanorm{
  \edef\tucp@ster@scale{4}
  \edef\tucp@ster@paperwidth{925mm}
  \edef\tucp@ster@paperheight{1265mm}
  \edef\tucp@ster@lmargin{43mm}
  \edef\tucp@ster@rmargin{43mm}
  \edef\tucp@ster@headpreskip@simple{43mm}
  \edef\tucp@ster@headpreskip@fancy{43mm}
  \edef\tucp@ster@headpostskip@simple{43mm}
  \edef\tucp@ster@headpostskip@fancy{86mm}
  \edef\tucp@ster@headlogosep{43mm}
  \edef\tucp@ster@headlogowidth{200mm}
  \edef\tucp@ster@headrule{4pt}
  \edef\tucp@ster@headnormalsize{66}
  \edef\tucp@ster@footheight@default{84mm}
  % Logo-Höhe: 60.5mm
  % Logo-Abstand: 0.5 * (Höhe Fußzeile - Logo-Höhe)
  \edef\tucp@ster@footmargin@default{11.75mm}
  \edef\tucp@ster@footrule@default{4pt}
  \edef\tucp@ster@footnormalsize{36}
  \edef\tucp@ster@fancytitle@size{75pt}
  \edef\tucp@ster@fancytitle@skip{92pt}
}

\def\tucp@ster@tpl@octanorml{
  \tucp@ster@tpl@octanorm
  \edef\tucp@ster@paperwidth{1265mm}
  \edef\tucp@ster@paperheight{925mm}
}


%
% Optionen abarbeiten.
%

% Template festlegen.
\define@choicekey{tucposter2019.cls}{template}{a0,a0l,a1,a1l,a2,a2l,a3,a3l,a4,a4l,octanorm,octanorml}[a0]{%
\csname tucp@ster@tpl@#1\endcsname}

% Hauptfarbe festlegen.
\define@choicekey{tucposter2019.cls}{fakcolor}{tuc,natwi,ma,mb,etit,if,wiwi,phil,hsw,gold,silver}[tuc]{%
\PassOptionsToPackage{fakcolor=#1}{beamercolorthemetuc2019}}

% Farbraum festlegen.
\define@choicekey{tucposter2019.cls}{colorspace}{rgb,cmyk}[rgb]{%
\PassOptionsToPackage{colorspace=#1}{beamercolorthemetuc2019}}

% Standard-Schriften verwenden.
\DeclareOption{latexfonts}{%
\PassOptionsToPackage{latexfonts}{beamerfontthemetuc2019}}
\DeclareOption{latexfontsbody}{%
\PassOptionsToPackage{latexfontsbody}{beamerfontthemetuc2019}}

% Schrift skalieren.
\define@key{tucposter2019.cls}{scale}{%
\FPmul{\tucp@ster@scale}{\tucp@ster@scale}{#1}}

% Alle weiteren Optionen an die Basisklasse durchreichen.
\DeclareOptionX*{\PassOptionsToClass{\CurrentOption}{beamer}}

% Frames per Default an der Oberkante ausrichten.
\PassOptionsToClass{t}{beamer}

% Optionen bearbeiten.
\ExecuteOptionsX{template=a0}
\ProcessOptionsX\relax

%
% Basisklasse laden.
%
\LoadClass{beamer}


%
% Satzspiegel festlegen.
%
\RequirePackage{geometry}
\geometry{paperwidth=\tucp@ster@paperwidth,paperheight=\tucp@ster@paperheight,left=0mm,right=0mm,top=0mm,bottom=0pt,noheadfoot,nomarginpar}
\setbeamersize{text margin left=0pt,text margin right=0pt,sidebar width left=0pt,sidebar width right=0pt}


% Einen Glue skalieren.
% (http://tex.stackexchange.com/questions/198954/scaling-a-glue-in-tex)
\newcommand{\tucp@ster@scaleglue}[3]{#3=\glueexpr#2*\numexpr\dimexpr#1pt\relax\relax/65536\relax}

%
% Schriftgröße und Maße anpassen.
%
% Hier werden die Schriftgrößenbefehle neu definiert. Dies geschieht durch
% \protected@xdef. Dieses Makro expandiert dabei seine Definition und wirkt
% global. Achtung alle anderen Einstellungen (z.B. \@listi) werden geplättet
% und sollten vorher gesichert werden.
%
\newcommand{\tucp@ster@redeffontsize}[1]
{\begingroup
\csname #1\endcsname
\setlength{\@tempdima}{\f@baselineskip}
\edef\f@bskip{\strip@pt\@tempdima}
\FPupn{\loc@fsize@}{f@size  tucp@ster@scale * 2 round}
\FPupn{\loc@bskip@}{f@bskip tucp@ster@scale * 2 round}
\locskip\loc@ads@\tucp@ster@scaleglue{\tucp@ster@scale}{\abovedisplayskip}{\loc@ads@}
\locskip\loc@bds@\tucp@ster@scaleglue{\tucp@ster@scale}{\belowdisplayskip}{\loc@bds@}
\locskip\loc@adss@\tucp@ster@scaleglue{\tucp@ster@scale}{\abovedisplayshortskip}{\loc@adss@}
\locskip\loc@bdss@\tucp@ster@scaleglue{\tucp@ster@scale}{\belowdisplayshortskip}{\loc@bdss@}
\expandafter\protected@xdef\csname #1\endcsname{%
\@setfontsize\normalsize{\loc@fsize@}{\loc@bskip@}%
\setlength{\abovedisplayskip}{\the\loc@ads@}%
\setlength{\belowdisplayskip}{\the\loc@bds@}%
\setlength{\abovedisplayshortskip}{\the\loc@adss@}%
\setlength{\belowdisplayshortskip}{\the\loc@bdss@}}
\endgroup}

%
% Die Größenkommandos \small und \footnotesize definieren das Kommando \@listi
% welches abweichende Abstände bei Listen der ersten Gliederungstiefe
% einstellt. Diese Definitionen werden hier an die Schriftgrößenbefehle
% angehängt. Diese Makro darf demnach auch erst nach \tucp@ster@redeffontsize
% für die entsprechende Größe aufgerufen werden. Die vorherige
% \@listi-Definition muss zuvor in das Makro \tucp@ster@<Größe>@listi
% gesichert werden.
%
\newcommand{\tucp@ster@redeflisti}[1]
{\begingroup
\csname tucp@ster@#1@listi\endcsname
\locskip\loc@topsep@\tucp@ster@scaleglue{\tucp@ster@scale}{\topsep}{\loc@topsep@}
\locskip\loc@parsep@\tucp@ster@scaleglue{\tucp@ster@scale}{\parsep}{\loc@parsep@}
\def\loc@listi@{%
\setlength{\leftmargin}{\leftmargini}
\setlength{\topsep}{\the\loc@topsep@}
\setlength{\parsep}{\the\loc@parsep@}
\setlength{\itemsep}{\parsep}}
\expandafter\protected@xdef\csname #1\endcsname{\csname #1\endcsname\noexpand\def\noexpand\@itemi{\loc@listi@}}
\endgroup}

%
% Das hier funktioniert analog zu oben, nur das die Definitionen global
% vorgenommen werden und nicht an das Schriftgrößenmakro angefügt werden.
%
\newcommand{\tucp@ster@redeflists}[1]
{\begingroup\csname @list#1\endcsname
\locskip\loc@topsep@\tucp@ster@scaleglue{\tucp@ster@scale}{\topsep}{\loc@topsep@}
\locskip\loc@parsep@\tucp@ster@scaleglue{\tucp@ster@scale}{\parsep}{\loc@parsep@}
\locskip\loc@itemsep@\tucp@ster@scaleglue{\tucp@ster@scale}{\itemsep}{\loc@itemsep@}
\expandafter\protected@xdef\csname @list#1\endcsname{%
\leftmargin\csname leftmargin#1\endcsname%
\topsep\the\loc@topsep@%
\parsep\the\loc@parsep@%
\itemsep\the\loc@itemsep@}
\endgroup}

% Die \@listi-Einstellungen sichern.
\begingroup\small\global\let\tucp@ster@small@listi\@listi\endgroup
\begingroup\footnotesize\global\let\tucp@ster@footnotesize@listi\@listi\endgroup

\tucp@ster@redeffontsize{tiny}
\tucp@ster@redeffontsize{scriptsize}
\tucp@ster@redeffontsize{footnotesize}
\tucp@ster@redeffontsize{small}
\tucp@ster@redeffontsize{normalsize}
\tucp@ster@redeffontsize{large}
\tucp@ster@redeffontsize{Large}
\tucp@ster@redeffontsize{LARGE}
\tucp@ster@redeffontsize{huge}
\tucp@ster@redeffontsize{Huge}

% Die \@listi-Einstellungen anpassen und hinterher aufräumen.
\g@addto@macro{\normalsize}{\let\@listi\@listI}
\normalsize
\tucp@ster@redeflisti{footnotesize}
\tucp@ster@redeflisti{small}
\global\let\tucp@ster@small@listi\@undefined
\global\let\tucp@ster@footnotesize@listi\@undefined

% Vert. Abstände anpassen.
\tucp@ster@scaleglue{\tucp@ster@scale}{\smallskipamount}{\smallskipamount}
\tucp@ster@scaleglue{\tucp@ster@scale}{\medskipamount}{\medskipamount}
\tucp@ster@scaleglue{\tucp@ster@scale}{\bigskipamount}{\bigskipamount}

%
% Jetzt die eigentlichen Listeneinstellungen anpassen. Die Makros \@listiv,
% \@listv, \@listvi legen normalerweise keine absoluten Maße fest, sondern
% bedienen sich aus bestehenden Längenregistern.
%
\tucp@ster@redeflists{i}
\tucp@ster@redeflists{ii}
\tucp@ster@redeflists{iii}
\let\@listI\@listi

% Listeneinzüge anpassen
\setlength\leftmargini{2em}
\setlength\leftmarginii{2em}
\setlength\leftmarginiii{2em}
\setlength\labelsep{.5em}
\setlength\labelwidth{\leftmargini}
\addtolength\labelwidth{-\labelsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\beamer@descriptionwidth}{\beamer@descriptionwidth}

% Gleitumgebungen anpassen
\tucp@ster@scaleglue{\tucp@ster@scale}{\footnotesep}{\footnotesep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\floatsep}{\floatsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\textfloatsep}{\textfloatsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\intextsep}{\intextsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\dblfloatsep}{\dblfloatsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\dbltextfloatsep}{\dbltextfloatsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\@fptop}{\@fptop}
\tucp@ster@scaleglue{\tucp@ster@scale}{\@fpsep}{\@fpsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\@fpbot}{\@fpbot}
\tucp@ster@scaleglue{\tucp@ster@scale}{\@dblfptop}{\@dblfptop}
\tucp@ster@scaleglue{\tucp@ster@scale}{\@dblfpsep}{\@dblfpsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\@dblfpbot}{\@dblfpbot}

% Tabellen anpassen
\tucp@ster@scaleglue{\tucp@ster@scale}{\arraycolsep}{\arraycolsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\tabcolsep}{\tabcolsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\arrayrulewidth}{\arrayrulewidth}
\tucp@ster@scaleglue{\tucp@ster@scale}{\doublerulesep}{\doublerulesep}
% \tabbingsep basiert auf \labelsep --> in em definiert --> auslassen

% Rahmen anpassen
\tucp@ster@scaleglue{\tucp@ster@scale}{\fboxsep}{\fboxsep}
\tucp@ster@scaleglue{\tucp@ster@scale}{\fboxrule}{\fboxrule}

% Beschriftungen anpassen
\tucp@ster@scaleglue{\tucp@ster@scale}{\abovecaptionskip}{\abovecaptionskip}
\tucp@ster@scaleglue{\tucp@ster@scale}{\belowcaptionskip}{\belowcaptionskip}


%
% Öffentliche Längenregister anlegen.
%
\newlength{\tucplogosep}	% Logo-Schutzraum
\newlength{\tucplogowidth}	% Logo-Breite
\newlength{\tucplogoheight}	% Logo-Höhe
\newlength{\tucprulethickness}	% Dicke der Trennlinien
\newlength{\tucpheadlineindent}	% Einzug für die Kopfzeilen
\newlength{\tucpsmallsep}	% Kleiner Abstand

\setlength{\tucplogosep}{\tucp@ster@headlogosep}
\setlength{\tucplogowidth}{\tucp@ster@headlogowidth}
\setlength{\tucprulethickness}{\tucp@ster@headrule}
\setlength{\tucpsmallsep}{.5838150289\tucplogosep}	% 101/173 * Schutzraum


%
% Nun wurden die Templates geladen und wir können Einstellungen festlegen,
% die für alle Templates gelten.
%
\begingroup

% Höhe des Logos aus dem Bild ausmessen.
\locbox\@tempbox
\savebox\@tempbox{\includegraphics[width=\tucplogowidth]{tuc2019/logo/tuc_white}}
\setlength{\tucplogoheight}{\ht\@tempbox}
\global\tucplogoheight=\tucplogoheight
\global\edef\tucp@ster@headlogoheight{\the\tucplogoheight}

% Einzug der Kopfzeilen
% = linker Rand + 2 * Schutzraum + Logobreite
\setlength{\tucpheadlineindent}{0pt}
\addtolength{\tucpheadlineindent}{\tucp@ster@lmargin}
\addtolength{\tucpheadlineindent}{\tucp@ster@headlogosep}
\addtolength{\tucpheadlineindent}{\tucp@ster@headlogowidth}
\addtolength{\tucpheadlineindent}{\tucp@ster@headlogosep}
\global\tucpheadlineindent=\tucpheadlineindent
\global\edef\tucp@ster@headlineindent{\the\tucpheadlineindent}

% Länge der Kopfzeilen
% = Papierbreite - Einzug - rechter Rand
\setlength{\@tempdima}{\tucp@ster@paperwidth}
\addtolength{\@tempdima}{-\tucpheadlineindent}
\addtolength{\@tempdima}{-\tucp@ster@rmargin}
\global\edef\tucp@ster@headlinewidth{\the\@tempdima}

% Einzüge und Abstände von Absatzblöcken mit seitlichen Überschriften
\global\edef\tucp@ster@sbilsep{\the\tucpsmallsep}
\global\edef\tucp@ster@sbirsep{\the\tucpsmallsep}
\global\edef\tucp@ster@sbolsep{\tucp@ster@lmargin}
\global\edef\tucp@ster@sborsep{\tucp@ster@rmargin}
\global\edef\tucp@ster@sbtopsep{\the\tucpsmallsep}
\global\edef\tucp@ster@sbbotsep{\the\tucpsmallsep}
\global\edef\tucp@ster@sbilsep@org{\tucp@ster@sbilsep}
\global\edef\tucp@ster@sbirsep@org{\tucp@ster@sbirsep}
\global\edef\tucp@ster@sbolsep@org{\tucp@ster@sbolsep}
\global\edef\tucp@ster@sborsep@org{\tucp@ster@sborsep}
\global\edef\tucp@ster@sbtopsep@org{\tucp@ster@sbtopsep}
\global\edef\tucp@ster@sbbotsep@org{\tucp@ster@sbbotsep}

% Höhe des Titelblocks von Themenpostern
% = 0.5 * Logohöhe + 2 * Logoschutzraum
\setlength{\@tempdima}{\tucp@ster@headlogoheight}
\setlength{\@tempdima}{0.5\@tempdima}
\addtolength{\@tempdima}{\tucp@ster@headlogosep}
\addtolength{\@tempdima}{\tucp@ster@headlogosep}
\global\edef\tucp@ster@fancytitleheight{\the\@tempdima}

\endgroup


%
% Themes laden.
%
\usefonttheme{professionalfonts}
\usecolortheme{tuc2019}
\usefonttheme{tuc2019}
\useinnertheme{tuc2019}

% Verhindern, dass ein Outer-Theme geladen werden kann.
\global\let\userbeameroutertheme\@undefined


%
% Farben festlegen.
%
\setbeamercolor*{tucp head}{use=structure,fg=white,bg=structure.fg}
\setbeamercolor*{tucp foot}{use=structure,fg=structure.fg,bg=white}
\setbeamercolor*{tucp foot rule}{use=tucp seprule,bg=tucp seprule.fg}
\setbeamercolor*{tucp simpletitle}{parent=structure,bg=white}
\setbeamercolor*{tucp simpletitle title}{}
\setbeamercolor*{tucp simpletitle subtitle}{}
\setbeamercolor*{tucp simpletitle author}{}
%\setbeamercolor*{tucp simpleabstract}{parent=structure,bg=white} %TODO
\setbeamercolor*{tucp fancytitle}{fg=tuccolor@silver,bg=white}
\setbeamercolor*{tucp fancytitle line1}{parent=tucp fancytitle}
\setbeamercolor*{tucp fancytitle line2}{parent=tucp fancytitle}
\setbeamercolor*{tucp fancytitle line3}{parent=tucp fancytitle}
\setbeamercolor*{tucp fancyabstract}{parent=tucp head}
\setbeamercolor*{tucp section}{use=structure,fg=structure.fg,bg=structure.fg!10!white}
\setbeamercolor*{tucp sectionblock}{}
\setbeamercolor*{tucp sectionblock header}{fg=white,bg=tuccolor@silver!50!white}
\setbeamercolor*{tucp sectionblock header left}{parent=tucp sectionblock header}
\setbeamercolor*{tucp sectionblock header right}{parent=tucp sectionblock header}
\setbeamercolor*{tucp seprule}{fg=tuccolor@silver}
\setbeamercolor*{tucp column seprule}{parent=tucp seprule}

\setbeamercolor*{block title}{use=structure,fg=white,bg=structure.fg}
\setbeamercolor*{block title alerted}{use=alerted text,fg=white,bg=alerted text.fg}
\setbeamercolor*{block title example}{use=example text,fg=white,bg=example text.fg}

\setbeamercolor*{block body}{parent=normal text,use=block title,bg=block title.bg!10!bg}
\setbeamercolor*{block body alerted}{parent=normal text,use=block title alerted,bg=block title alerted.bg!10!bg}
\setbeamercolor*{block body example}{parent=normal text,use=block title example,bg=block title example.bg!10!bg}


%
% Fonts festlegen.
%
\setbeamerfont*{tucp head}{size=\tucpheadsizenormal}
\setbeamerfont*{tucp foot}{size=\tucpfootsizenormal}
\setbeamerfont*{tucp simpletitle}{}
\setbeamerfont*{tucp simpletitle title}{parent=tucp simpletitle,size=\huge}
\setbeamerfont*{tucp simpletitle subtitle}{parent=tucp simpletitle,size=\Large}
\setbeamerfont*{tucp simpletitle author}{parent=tucp simpletitle,size=\normalsize}
%\setbeamerfont*{tucp simpleabstract}{} %TODO
\setbeamerfont*{tucp fancytitle}{size*={\tucp@ster@fancytitle@size}{\tucp@ster@fancytitle@skip}}
\setbeamerfont*{tucp fancytitle line1}{parent=tucp fancytitle,series=\bfseries}
\setbeamerfont*{tucp fancytitle line2}{parent=tucp fancytitle}
\setbeamerfont*{tucp fancytitle line3}{parent=tucp fancytitle}
\setbeamerfont*{tucp fancyabstract}{}
\setbeamerfont*{tucp section}{}
\setbeamerfont*{tucp sectionblock}{}
\setbeamerfont*{tucp sectionblock header}{}
\setbeamerfont*{tucp sectionblock header left}{parent=tucp sectionblock header}
\setbeamerfont*{tucp sectionblock header right}{parent=tucp sectionblock header}


%
% Am Anfang des Dokuments Roboto-Schriften laden, da das Font-Theme
% überschrieben werden kann, wenn der Nutzer weitere Schriftpakete lädt.
%
\g@addto@macro\beamer@firstminutepatches{
\global\def\rmdefault{\robotoslabfamily}
\global\def\sfdefault{\robotofamily}
\IfFileExists{roboto-mono.sty}{\global\def\ttdefault{\robotomonofamily}}{\relax}}


%
% Kein \parskip an Anfang eines Frames einfügen.
%
\g@addto@macro\beamer@lastminutepatches{
\tucpnofirstparskip}


%
% Weitere Pakete laden.
%
\RequirePackage{parskip}
\RequirePackage{xcolor}
\RequirePackage{calc}
\RequirePackage{graphicx}
\RequirePackage{changepage}
\RequirePackage{ragged2e}
\RequirePackage{xifthen}
\RequirePackage{multicol}
\RequirePackage{graphicx}
\RequirePackage{lmodern}
\RequirePackage{url}

\DeclareSymbolFont{largesymbols}{OMX}{cmex}{m}{n}


% TODO: Einzüge festlegen.
\AtBeginDocument{\justifying}
\g@addto@macro{\itemize}{\justifying}
\g@addto@macro{\beamer@enum@}{\justifying}
\g@addto@macro{\@@description}{\justifying}


%
% Die nicht benötigten Beamer-Elemente ausblenden.
%
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{left sidebar}{}
\setbeamertemplate{right sidebar}{}
\setbeamertemplate{left canvas sidebar}{}
\setbeamertemplate{right canvas sidebar}{}


%
% \parskip vor einem Absatz aufheben.
%
\newlength{\tucpparskip}
\setlength{\tucpparskip}{\parskip}

\def\@minipagerestore{\parskip=\tucpparskip}

\newcommand{\tucpnofirstparskip}{\ignorespaces}
\newcommand{\tucpnofirstparskipoff}{\renewcommand{\tucpnofirstparskip}{\ignorespaces}}%
\newcommand{\tucpnofirstparskipon}{\renewcommand{\tucpnofirstparskip}{%
\par%
%\ifdim\parskip>0pt\setlength{\tucpparskip}{\parskip}\fi%
\setlength{\parskip}{0pt}%
\everypar{\setlength{\parskip}{\tucpparskip}\everypar{}}%
\nointerlineskip}\ignorespaces}%

\tucpnofirstparskipon

%\newcommand{\tucpinsertparskip}{\vspace*{\tucpparskip}}
\newcommand{\tucpcancelparskip}{\vspace*{-\parskip}\nointerlineskip}


%
% Kopf- und Fußzeile neu ausmessen
%
\newcommand{\tucprecalcheadfoot}{\beamer@calculateheadfoot%
\aftergroup\beamer@calculateheadfoot}


%
% Die 4pt Abstand zwischen Fußzeile und Textkörper rückgängig machen, die
% LaTeX-Beamer hier zwangsläufig einfügt.
%
\g@addto@macro\beamer@calculateheadfoot{%
\advance\footheight by -4pt%
\footskip=\footheight%
\advance\textheight by 4pt%
\@colht\textheight%
\@colroom\textheight%
\vsize\textheight}


%
% Kopfzeile
%
\defbeamertemplate*{headline}{normal}
{%
  \begin{beamercolorbox}[vmode]{tucp head}%
  \vskip\tucp@ster@headpreskip\relax%
  \hbox to \hsize{%
    \hskip\tucp@ster@lmargin%
    \includegraphics[width=\tucp@ster@headlogowidth]{tuc2019/logo/tuc_white}%
    \hskip\tucp@ster@headlogosep%
    \setlength{\@tempdima}{\tucp@ster@headrule}%
    \hskip-0.5\@tempdima%
    \vrule width \tucp@ster@headrule%
    \hskip-0.5\@tempdima%
    \hskip\tucp@ster@headlogosep%
    \begin{minipage}[b][\tucp@ster@headlogoheight][\tucp@ster@head@placement]{\tucp@ster@headlinewidth}%
    \setlength{\vsize}{\tucp@ster@headlogoheight}%
    \begingroup%
    \usebeamercolor{tucp head}%
    \usebeamerfont{tucp head}%
    \parskip=0pt\lineskiplimit=0pt%
    \tucp@ster@head@content\par%
    \endgroup%
    \end{minipage}%
    \hfill\hskip\tucp@ster@rmargin}%
  \vskip\tucp@ster@headpostskip\relax%
  \end{beamercolorbox}%
}


\newcommand{\tucpsimplehead}{%
\edef\tucp@ster@headpreskip{\tucp@ster@headpreskip@simple}
\edef\tucp@ster@headpostskip{\tucp@ster@headpostskip@simple}
\setbeamertemplate{headline}[normal]%
\tucprecalcheadfoot}

\newcommand{\tucpfancyhead}{%
\edef\tucp@ster@headpreskip{\tucp@ster@headpreskip@fancy}
\edef\tucp@ster@headpostskip{\tucp@ster@headpostskip@fancy}
\setbeamertemplate{headline}[normal]%
\tucprecalcheadfoot}

\edef\tucp@ster@headpreskip{\tucp@ster@headpreskip@simple}
\edef\tucp@ster@headpostskip{\tucp@ster@headpostskip@simple}

\newcommand{\tucphead}[2][t]{%
\def\tucp@ster@head@placement{#1}%
\def\tucp@ster@head@content{#2}}
\tucphead{\relax}

\newcommand{\tucp@ster@redefheadfootsize}[4]
{\begingroup
\edef\loc@fsize{#2}
\edef\loc@scale{#3}
\edef\loc@bscale{#4}
\FPupn{\loc@fsize@}{loc@fsize loc@scale * 2 round}
\FPupn{\loc@bskip@}{loc@fsize loc@scale loc@bscale * * 2 round}
\expandafter\protected@xdef\csname #1\endcsname{%
\fontsize{\loc@fsize@}{\loc@bskip@}\selectfont}
\endgroup}

\tucp@ster@redefheadfootsize{tucpheadsizenormal}{\tucp@ster@headnormalsize}{1}{1.18}
\tucp@ster@redefheadfootsize{tucpheadsizelarge}{\tucp@ster@headnormalsize}{1.2}{1.18}
\tucp@ster@redefheadfootsize{tucpheadsizeLarge}{\tucp@ster@headnormalsize}{1.44}{1.18}
\tucp@ster@redefheadfootsize{tucpfootsizenormal}{\tucp@ster@footnormalsize}{1}{1.34}
\tucp@ster@redefheadfootsize{tucpfootsizelarge}{\tucp@ster@footnormalsize}{1.2}{1.34}
\tucp@ster@redefheadfootsize{tucpfootsizeLarge}{\tucp@ster@footnormalsize}{1.44}{1.34}


%
% Fußzeile
%
\defbeamertemplate{footline}{empty}{}
\defbeamertemplate*{footline}{normal}
{%
  \ifdim\tucp@ster@footrule>0pt%
  \begin{beamercolorbox}[ht=\tucp@ster@footrule]{tucp foot rule}
  \end{beamercolorbox}
  \fi%
  \begin{beamercolorbox}[vmode]{tucp foot}%
  \usebeamerfont{tucp foot}%
  \locdimen\@tempwidth%
  \setlength{\@tempwidth}{\hsize}%
  \addtolength{\@tempwidth}{-\tucp@ster@lmargin}%
  \addtolength{\@tempwidth}{-\tucp@ster@rmargin}%
  \locdimen\@tempheight%
  \setlength{\@tempheight}{\tucp@ster@footheight}%
  \addtolength{\@tempheight}{-\tucp@ster@footmargin}%
  \addtolength{\@tempheight}{-\tucp@ster@footmargin}%
  \vbox to \tucp@ster@footheight{%
    \vskip\tucp@ster@footmargin plus 1fil\relax%
    \hbox to \hsize{\hfill\hbox to \@tempwidth{%
      \setlength{\hsize}{\@tempwidth}%
      \setlength{\vsize}{\@tempheight}%
      \tucp@ster@foot@content}%
    \hfill}%
    \vskip\tucp@ster@footmargin plus 1fil\relax}%
  \end{beamercolorbox}%
}

% Fußzeile ausschalten.
\newcommand{\tucpfootoff}{%
\setbeamertemplate{footline}[empty]%
\tucprecalcheadfoot}

% Inhalt für Standardfußzeile festlegen.
\newcommand{\tucp@ster@foot@set@normal}[2]{%
\def\tucp@ster@foot@content{%
\rlap{$\vcenter{\hbox{#1}}$}\hfill%
\llap{$\vcenter{\vbox{#2}}$}}}

% Logos in der Fußzeile vertikal zentrieren.
\newcommand{\tucpfootlogo}[1]{$\vcenter{\hbox{#1}}$}

% URL in normaler Schrift anzeigen.
\newcommand{\tucpfooturl}[1]{\llap{\hbox{\urlstyle{same}\strut\url{#1}\strut}}}

% Standardfußzeile aktivieren.
\newcommand{\tucpfoot}[3][\tucp@ster@footheight@default]{%
\edef\tucp@ster@footheight{#1}%
\setbeamertemplate{footline}[normal]%
\tucp@ster@foot@set@normal{#2}{#3}%
\tucprecalcheadfoot}

% Individuelle Fußzeile aktivieren.
\newcommand{\tucprawfoot}[2][\tucp@ster@footheight@default]{%
\edef\tucp@ster@footheight{#1}%
\setbeamertemplate{footline}[normal]%
\def\tucp@ster@foot@content{\vbox{#2}}%
\tucprecalcheadfoot}

% Höhe festlegen.
\newcommand{\tucpfootheight}[1][\tucp@ster@footheight@default]{%
\edef\tucp@ster@footheight{#1}%
\tucprecalcheadfoot}

% Vert. Rand festlegen.
\newcommand{\tucpfootmargin}[1][\tucp@ster@footmargin@default]{%
\edef\tucp@ster@footmargin{#1}%
\tucprecalcheadfoot}

% Trennlinie festlegen.
\newcommand{\tucpfootrule}[1][\tucp@ster@footrule@default]{%
\edef\tucp@ster@footrule{#1}%
\tucprecalcheadfoot}

% Voreinstellungen für die Fußzeile festlegen.
\edef\tucp@ster@footheight{\tucp@ster@footheight@default}
\edef\tucp@ster@footmargin{\tucp@ster@footmargin@default}
\edef\tucp@ster@footrule{\tucp@ster@footrule@default}
\tucp@ster@foot@set@normal{\relax}{\tucpfooturl{https://www.tu-chemnitz.de/}}


%
% Die Ausrichtung innerhalb der frame-Umgebung festlegen.
%
\define@key{beamerframe}{c}[true]{% centered
  \beamer@frametopskip=0pt plus 1fill\relax%
  \beamer@framebottomskip=0pt plus 1.5fill\relax%
  \beamer@frametopskipautobreak=0pt\relax%
  \beamer@framebottomskipautobreak=0pt\relax%
  % Kompatibilität zu alten Beamer-Versionen
  \def\beamer@initfirstlineunskip{\vskip\parskip\vskip0pt\nointerlineskip}%
}
\define@key{beamerframe}{t}[true]{% top
  \beamer@frametopskip=0pt\relax%
  \beamer@framebottomskip=0pt plus 1fil\relax%
  \beamer@frametopskipautobreak=\beamer@frametopskip\relax%
  \beamer@framebottomskipautobreak=\beamer@framebottomskip\relax%
  % Kompatibilität zu alten Beamer-Versionen
  \def\beamer@initfirstlineunskip{\vskip\parskip\vskip0pt\nointerlineskip}%
}
\define@key{beamerframe}{b}[true]{% bottom
  \beamer@frametopskip=0pt plus 1fil\relax%
  \beamer@framebottomskip=0pt\relax%
  \beamer@frametopskipautobreak=\beamer@frametopskip\relax%
  \beamer@framebottomskipautobreak=\beamer@framebottomskip\relax%
  % Kompatibilität zu alten Beamer-Versionen
  \def\beamer@initfirstlineunskip{\vskip\parskip\vskip0pt\nointerlineskip}%
}
\define@key{beamerframe}{j}[true]{% justifying
  \beamer@frametopskip=0pt\relax%
  \beamer@framebottomskip=0pt\relax%
  \beamer@frametopskipautobreak=\beamer@frametopskip\relax%
  \beamer@framebottomskipautobreak=\beamer@framebottomskip\relax%
  % Kompatibilität zu alten Beamer-Versionen
  \def\beamer@initfirstlineunskip{\vskip\parskip\vskip0pt\nointerlineskip}%
}


%
% Tiefe einer Box entfernen.
%
% Damit die Unterkanten zweier horizontal benachbarter Blöcke bündig
% erscheinen, kann es notwendig sein, die Tiefe einer Box zu entfernen. Somit
% werden die Unterlängen von Buchstaben entfernt und Boxen können an der
% Grundlinie ihrer letzten Zeile ausgerichtet werden.
%
\newenvironment{tucpcanceldepth}[1][\maxdimen]
{%
  \begingroup%
  \locdimen\@tempdim%
  \setlength{\@tempdim}{#1}%
  \locbox\@tempbox%
  \setbox\@tempbox\vbox\bgroup%
}
{%
  \egroup%
  \ifdim\dp\@tempbox>\@tempdim%
  \setlength{\@tempdim}{-\@tempdim}%
  \addtolength{\@tempdim}{\ht\@tempbox}%
  \addtolength{\@tempdim}{\dp\@tempbox}%
  \setlength{\ht\@tempbox}{\@tempdim}\fi%
  \setlength{\dp\@tempbox}{0pt}%
  \usebox{\@tempbox}%
  \endgroup%
}


%
% Farbbox
%
\newenvironment{tucpcolorblock}[2][]
{\tucpnofirstparskip\beamercolorbox[sep=0pt,#1]{#2}\justifying}%
{\endbeamercolorbox\aftergroup\tucpnofirstparskip}


%
% multicol-Umgebung anpassen
%
\setlength{\columnsep}{\tucp@ster@headlogosep}
\setlength{\columnsep}{0.5\columnsep}
\renewcommand{\columnseprulecolor}{\usebeamercolor{tucp column seprule}\color{fg}}

\newcommand{\tucpcolumnsepruleon}{\setlength{\columnseprule}{\tucp@ster@headrule}}
\newcommand{\tucpcolumnsepruleoff}{\setlength{\columnseprule}{0pt}}
\tucpcolumnsepruleoff


%
% Eine \vbox mit linkem und rechtem Einzug.
%
\newenvironment{tucpmarginblock}[3][]
{%
  \par\nointerlineskip%
  \begingroup%
  \locdimen\@tempdim%
  \locdimen\@templmargin%
  \locdimen\@temprmargin%
  \ifthenelse{\isempty{#1}}%
  {\def\tucp@ster@mbbox{\vbox}\def\tucp@ster@mbvsize{\relax}}%
  {\def\tucp@ster@mbbox{\vbox to #1}\def\tucp@ster@mbvsize{\setlength{\vsize}{#1}}}%
  \setlength{\@templmargin}{#2}%
  \setlength{\@temprmargin}{#3}%
  \setlength{\@tempdim}{\linewidth}%
  \addtolength{\@tempdim}{-\@templmargin}%
  \addtolength{\@tempdim}{-\@temprmargin}%
  \hbox to \hsize\bgroup%
  \hskip\@templmargin%
  \tucp@ster@mbbox\bgroup\tucp@ster@mbvsize%
  \hsize=\@tempdim%
  \textwidth=\hsize\linewidth=\hsize\columnwidth=\hsize%
  \tucpnofirstparskip%
}
{%
  \egroup\hfill\egroup%
  \par\nointerlineskip%
  \endgroup%
  \aftergroup\tucpnofirstparskip%
}


%
% Einzug für Textblock
%
\newenvironment{tucptextindent}%
{\tucpnofirstparskip%
\adjustwidth{\tucp@ster@lmargin}{\tucp@ster@rmargin}}%
{\endadjustwidth\aftergroup\tucpnofirstparskip}

\newenvironment{tucptextblock}[1][]%
{\tucpmarginblock[#1]{\tucp@ster@lmargin}{\tucp@ster@rmargin}}%
{\endtucpmarginblock}


%
% Einzug für Themenposter
%
\newenvironment{tucpfancyindent}%
{\tucpnofirstparskip%
\adjustwidth{\tucp@ster@headlineindent}{\tucp@ster@rmargin}}%
{\endadjustwidth\aftergroup\tucpnofirstparskip}

\newenvironment{tucpfancyblock}[1][]%
{\tucpmarginblock[#1]{\tucp@ster@headlineindent}{\tucp@ster@rmargin}}%
{\endtucpmarginblock}


%
% Einfacher Titelblock
%
% TODO: Abstände templaten.
%
\defbeamertemplate*{tucp simpletitle title}{default}{%
\inserttitle\par}

\defbeamertemplate*{tucp simpletitle subtitle}{default}{%
\ifx\insertsubtitle\@empty\else%
{\usebeamerfont{tucp simpletitle title}\vspace{1ex}}%
\insertsubtitle\par\fi}

\defbeamertemplate*{tucp simpletitle author}{default}{%
\ifx\insertauthor\@empty\else%
{\usebeamerfont{tucp simpletitle title}\vspace{1ex}}%
\insertauthor\par\fi}

\defbeamertemplate{tucp simpletitle}{subtitle}
{
  \vspace*{\tucplogosep}
  \begin{center}
  \usebeamertemplate*{tucp simpletitle title}
  \usebeamertemplate*{tucp simpletitle subtitle}
  \end{center}
  \vspace*{0.8\tucplogosep}
}

\defbeamertemplate{tucp simpletitle}{author}
{%
  \vspace*{\tucplogosep}
  \begin{center}
  \usebeamertemplate*{tucp simpletitle title}
  \usebeamertemplate*{tucp simpletitle author}
  \end{center}
  \vspace*{0.8\tucplogosep}
}

\defbeamertemplate{tucp simpletitle}{subtitleauthor}
{%
  \vspace*{\tucplogosep}
  \begin{center}
  \usebeamertemplate*{tucp simpletitle title}
  \usebeamertemplate*{tucp simpletitle subtitle}
  \usebeamertemplate*{tucp simpletitle author}
  \end{center}
  \vspace*{0.8\tucplogosep}
}

\defbeamertemplate{tucp simpletitle}{authorsubtitle}
{%
  \vspace*{\tucplogosep}
  \begin{center}
  \usebeamertemplate*{tucp simpletitle title}
  \usebeamertemplate*{tucp simpletitle author}
  \usebeamertemplate*{tucp simpletitle subtitle}
  \end{center}
  \vspace*{0.8\tucplogosep}
}

\setbeamertemplate{tucp simpletitle}[authorsubtitle]

\newcommand{\tucpsimpletitle}{%
\begin{tucpcolorblock}[vmode]{tucp simpletitle}
\begin{tucptextblock}
\usebeamertemplate{tucp simpletitle}
\end{tucptextblock}
\end{tucpcolorblock}}


%
% Titelblock für Themenposter
%
\newcommand{\tucpfancytitle}[3]{%
\begin{tucpcolorblock}[vmode]{tucp fancytitle}
\vbox to \tucp@ster@fancytitleheight{%
\vspace*{0pt plus 1fil}%
\tucpfancyblock\raggedright%
\vbox{\usebeamerfont{tucp fancytitle}%
\hbox to \hsize{\usebeamercolor{tucp fancytitle line1}\usebeamerfont{tucp fancytitle line1}#1\hfil}
\hbox to \hsize{\usebeamercolor{tucp fancytitle line2}\usebeamerfont{tucp fancytitle line2}#2\hfil}
\hbox to \hsize{\usebeamercolor{tucp fancytitle line3}\usebeamerfont{tucp fancytitle line3}#3\hfil}}
\endtucpfancyblock%
\vspace*{0pt plus 2fil}}%
\end{tucpcolorblock}}


%
% Abstract für Themenposter
%
\newenvironment{tucpfancyabstract}[1][0.1875\paperheight]
{%
  \tucpcolorblock[vmode]{tucp fancyabstract}%
  \usebeamerfont{tucp fancyabstract}%
  \ifthenelse{\isempty{#1}}%
  {\def\tucp@ster@fabox{\vbox}}%
  {\def\tucp@ster@fabox{\vbox to #1}}%
  \begingroup%
  \tucpfancyblock%
  \tucp@ster@fabox\bgroup%
  \vskip\tucpsmallsep%
  \tucpnofirstparskip%
}
{%
  \vskip\tucpsmallsep%
  \vskip 0pt plus 1fil\egroup%
  \endtucpfancyblock%
  \endgroup%
  \endtucpcolorblock%
}


%
% Block mit seitlicher Überschrift
%
% Hier passiert ein bisschen schwarze Magie. Im Prinzip speichert die Umgebung
% ihren Inhalt in einer Box, die dann beim Beenden der Umgebung ausgegeben
% wird. Wir müssen folglich die Parameter in From von Makros ablegen, um bei
% Beendigung der Umgebung darauf zugreifen zu können. Um diese und alle
% weiteren Kommandos lokal zu halten, wir die gesamte Umgebung in einer Gruppe
% gekapselt.
%
% Abhängig davon, welche seitlichen Überschriften gesetzt werden sollen, wird
% die Breite der Inhaltsbox berechnet. Ggf. wird noch vertikaler Abstand als
% Rand eingefügt.
%
% Anschließend wird die Inhaltsbox konstruiert. Der Inhalt der Umgebung wird in
% einer \vbox platziert, sodass sich TeX im internen vertikalen Modus befindet.
% Das Einfügen von Tokens, die im vertikalen Modus verboten sind, führt zum
% Einfügen von \parskip in die \vbox und dem anschließenden Übergang in den
% horizontalen Modus. Das Einfügen des \parskip lässt sich leider nicht
% verhinden. Die gesamte Box wird durch eine \rule immer auf die endgültige
% Breite gespreizt, um später untervolle Boxen zu vermeiden.
%
% Der gesamte Block wird als \hbox konstruiert. Je nach Bedarf werden rechts
% und links Überschriften und die entsprechenden Abstände eingefügt. Die
% Inhaltsbox wird um den Betrag ihrer Tiefe angehoben, damit die Grundlinie
% mit dem unteren Rand des zu druckenden Materials übereinstimmt. Auf diese
% Weise wird eine korrekte Ausrichtung der Überschriften und des Inhalts
% erreicht.
%
\newcommand{\m@ketucpsbheader}[3]{%
\begingroup%
\usebeamercolor{#3}%
\usebeamerfont{#3}%
\setlength{\fboxsep}{0pt}%
\colorbox{bg}{%
\parbox[b][\vsize][c]{#1}{%
\hspace*{\fill}\rotatebox{90}{%
\vphantom{X}\smash{\textcolor{fg}{%
\hbox to \vsize{\hspace*{0pt plus 1fil}%
#2\hspace*{0pt plus 1fil}}}%
}}\hspace*{\fill}}}%
\endgroup}

\newenvironment{tucpsectionblock}[3][]
{%
  \par\nointerlineskip%
  \begingroup%
  \def\tucp@ster@sblname{#2}%
  \def\tucp@ster@sbrname{#3}%
  \locbox\@tempbox%
  \locdimen\@tempdim%
  \ifthenelse{\isempty{#1}}%
  {\def\tucp@ster@sbbox{\vbox}\def\tucp@ster@sbvsize{\relax}}%
  {\def\tucp@ster@sbbox{\vbox to #1}\def\tucp@ster@sbvsize{\setlength{\vsize}{#1}}}%
  \setlength{\@tempdim}{\linewidth}%
  \ifthenelse{\isempty{#2}}{%
  \let\tucp@ster@sblname\@empty%
  \addtolength{\@tempdim}{-\tucp@ster@sbolsep}}{%
  \addtolength{\@tempdim}{-\tucp@ster@sbolsep@org}%
  \addtolength{\@tempdim}{-\tucp@ster@sbilsep}}%
  \ifthenelse{\isempty{#3}}{%
  \let\tucp@ster@sbrname\@empty%
  \addtolength{\@tempdim}{-\tucp@ster@sborsep}}{%
  \addtolength{\@tempdim}{-\tucp@ster@sborsep@org}%
  \addtolength{\@tempdim}{-\tucp@ster@sbirsep}}%
  \setbox\@tempbox\vbox\bgroup%
  \hrule height 0pt width \@tempdim\relax%
  \tucp@ster@sbbox\bgroup\tucp@ster@sbvsize%
  \hsize=\@tempdim\textwidth=\hsize\linewidth=\hsize\columnwidth=\hsize%
  \leftskip=0pt\rightskip=0pt\parfillskip=0pt plus 1fil\relax%
  \usebeamerfont{tucp sectionblock}%
  \setlength{\@tempdim}{\tucp@ster@sbtopsep}%
  \ifdim\@tempdim=0pt\else\vskip\tucp@ster@sbtopsep\fi%
  \tucpnofirstparskip\ignorespaces%
}
{%
  \setlength{\@tempdim}{\tucp@ster@sbbotsep}%
  \ifdim\@tempdim=0pt\else\vskip\tucp@ster@sbbotsep\fi%
  \egroup\egroup%
  \begingroup%
  \setlength{\vsize}{\ht\@tempbox}%
  \addtolength{\vsize}{\dp\@tempbox}%
  \tucpcolorblock[vmode]{tucp sectionblock}%
  \hbox to \hsize{%
  \ifx\tucp@ster@sblname\@empty%
  \hspace*{\tucp@ster@sbolsep}\else%
  \m@ketucpsbheader{\tucp@ster@sbolsep@org}{\tucp@ster@sblname}{tucp sectionblock header left}%
  \hspace*{\tucp@ster@sbilsep}\fi%
  \raisebox{\dp\@tempbox}{\usebox{\@tempbox}}%
  \ifx\tucp@ster@sbrname\@empty%
  \hspace*{\tucp@ster@sborsep}\else%
  \hspace*{\tucp@ster@sbirsep}%
  \m@ketucpsbheader{\tucp@ster@sborsep@org}{\tucp@ster@sbrname}{tucp sectionblock header right}\fi}%
  \endtucpcolorblock%
  \endgroup%
  \endgroup%
  \aftergroup\tucpnofirstparskip%
}

\newcommand{\tucpsboutlsep}[1][\tucp@ster@sbolsep@org]{\edef\tucp@ster@sbolsep{#1}}
\newcommand{\tucpsboutrsep}[1][\tucp@ster@sborsep@org]{\edef\tucp@ster@sborsep{#1}}
\newcommand{\tucpsbinlsep}[1][\tucp@ster@sbilsep@org]{\edef\tucp@ster@sbilsep{#1}}
\newcommand{\tucpsbinrsep}[1][\tucp@ster@sbirsep@org]{\edef\tucp@ster@sbirsep{#1}}
\newcommand{\tucpsbtopsep}[1][\tucp@ster@sbtopsep@org]{\edef\tucp@ster@sbtopsep{#1}}
\newcommand{\tucpsbbotsep}[1][\tucp@ster@sbbotsep@org]{\edef\tucp@ster@sbbotsep{#1}}

\newcommand{\tucpsboutsepoff}{\tucpsboutlsep[0pt]\tucpsboutrsep[0pt]}
\newcommand{\tucpsboutsepon}{\tucpsboutlsep\tucpsboutrsep}
\newcommand{\tucpsbinsepoff}{\tucpsbinlsep[0pt]\tucpsbinrsep[0pt]\tucpsbtopsep[0pt]\tucpsbbotsep[0pt]}
\newcommand{\tucpsbinsepon}{\tucpsbinlsep\tucpsbinrsep\tucpsbtopsep\tucpsbbotsep}


%
% Begrenzungslinien
%
\newenvironment{tucprules}[1][\tucprulethickness]
{%
  \par\nointerlineskip%
  \begingroup%
  \locdimen\@tempdim%
  \setlength{\@tempdim}{#1}%
  \ifdim\lastskip>\@tempdim\vskip-\@tempdim\else\removelastskip\fi%
  {\usebeamercolor[fg]{tucp seprule}\hrule width \hsize height \@tempdim}%
  \tucpnofirstparskip%
}
{%
  \par\nointerlineskip%
  {\usebeamercolor[fg]{tucp seprule}\hrule width \hsize height \@tempdim}%
  \vskip-\@tempdim%
  \vskip\@tempdim%
  \endgroup%
  \aftergroup\tucpnofirstparskip%
}


%
% Überschrift
%
\newcommand{\tucpsection}[1]{%
\par\nointerlineskip\begingroup%
\setlength{\@tempdima}{\lastskip}%
\removelastskip%
\vbox{\setlength{\fboxsep}{0pt}%
\usebeamercolor{tucp section}%
\usebeamerfont{tucp section}%
\colorbox{bg}{%
\vbox to \tucp@ster@lmargin{%
\vfill\hbox to \hsize{\hspace*{0pt plus 1fil}%
\textcolor{fg}{\vphantom{X}\smash{#1}}%
\hspace*{0pt plus 1fil}}\vfill}}}%
\ifdim\@tempdima=0pt\else\vskip\@tempdima\fi%
\endgroup\par\tucpnofirstparskip\ignorespaces}

\newlength{\tucpsectionpreskipamount}
\newlength{\tucpsectionpostskipamount}
\setlength{\tucpsectionpreskipamount}{\tucplogosep}
\setlength{\tucpsectionpostskipamount}{0.618\tucplogosep}

\newcommand{\tucpsectionpreskip}{\vspace{\tucpsectionpreskipamount}}
\newcommand{\tucpsectionpostskip}{\vspace{\tucpsectionpostskipamount}}

\newcommand{\tucpsectionskip}[1]{%
\tucpsectionpreskip%
\tucpsection{#1}%
\tucpsectionpostskip}


%
% TODO:
%
% Umgebung simpleabstract
% Spalten
% Spalten mit Trennlinien
% Rahmen
% Große Mathe-Symbole
% Abstände skalieren: Lit.-Verz. ... ???
%

\endinput
