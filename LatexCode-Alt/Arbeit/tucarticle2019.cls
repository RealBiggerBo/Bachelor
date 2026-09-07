%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
% Klasse für Schriftstücke im Corporate Design 2019 der TU Chemnitz           %
% (c) Mario Haustein (mario.haustein@hrz.tu-chemnitz.de), 2013-2021           %
%                                                                             %
% Dieses Material steht unter der Creative-Commons-Lizenz Namensnennung -     %
% Keine Bearbeitungen 4.0 International. Um eine Kopie dieser Lizenz zu       %
% sehen, besuchen Sie http://creativecommons.org/licenses/by-nd/4.0/deed.de.  %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\ProvidesClass{tucarticle2019}[2022/05/17]

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

% Kopfzeile abschalten (für vorgedrucktes Briefpapier).
\newif\iftuc@head\tuc@headtrue
\DeclareOption{nohead}{\tuc@headfalse}

% Standard-Schriften verwenden.
\newif\iftuc@roboto\tuc@robototrue
\DeclareOption{latexfonts}{\tuc@robotofalse}

% Nicht auf linksbündig umschalten.
\newif\iftuc@flushleft\tuc@flushlefttrue
\DeclareOption{noflushleft}{\tuc@flushleftfalse}

% Keine Gesamtseitenanzahl angeben.
\newif\iftuc@totpages\tuc@totpagestrue
\DeclareOption{nototpages}{\tuc@totpagesfalse}

% Folgelogos ausschalten.
\newif\iftuc@contlogo\tuc@contlogotrue
\DeclareOption{nocontlogo}{\tuc@contlogofalse}


% Die restlichen Optionen an die Basisklasse weiterreichen.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{scrartcl}}

% Standard-Schriftgröße setzen.
\ExecuteOptions{11pt}

% Optionen verarbeiten.
\ProcessOptions*\relax

% Auf KOMA-Script aufbauen.
\LoadClass{scrartcl}


% Pakete laden.
\RequirePackage{etex}
\RequirePackage[a4paper]{geometry}
\RequirePackage{graphicx}
\RequirePackage{xcolor}
\RequirePackage{everyshi}
\RequirePackage{translations}
\RequirePackage{iflang}
\iftuc@totpages\RequirePackage{lastpage}\fi


%
% Farbe
%
\iftucblack
  \definecolor{tuccolor}{RGB}{0,0,0}
  \definecolor{tuccolor}{cmyk}{0.0,0.0,0.0,1.0}
  \iftuckhs
    \def\tuc@logo{%
      \IfLanguageName{english}%
        {tuc2019/logo/tuckhseng_black}%
        {tuc2019/logo/tuckhs_black}%
    }
  \else
    \def\tuc@logo{tuc2019/logo/tuc_black}
  \fi
\else
  \definecolor{tuccolor}{RGB}{0,95,80}
  \definecolor{tuccolor}{cmyk}{1.0,0.34,0.69,0.30}
  \iftuckhs
    \iftuckhscolor
      \def\tuc@logo{%
        \IfLanguageName{english}%
          {tuc2019/logo/tuckhseng_color}%
          {tuc2019/logo/tuckhs_color}%
      }
    \else
      \def\tuc@logo{%
        \IfLanguageName{english}%
          {tuc2019/logo/tuckhseng_green}%
          {tuc2019/logo/tuckhs_green}%
      }
    \fi
  \else
    \def\tuc@logo{tuc2019/logo/tuc_green}
  \fi
\fi


%
% Schrift laden.
%
\newkomafont{firstheadline}{\bfseries}
\newkomafont{nextheadline}{\mdseries}
\newkomafont{footline}{\relax}

\iftuc@roboto
\RequirePackage[default,sfdefault]{roboto}
\IfFileExists{roboto-mono.sty}{\RequirePackage{roboto-mono}}{\relax}

\setkomafont{firstheadline}{\robotomedium}
\setkomafont{nextheadline}{\robotoregular}
\setkomafont{footline}{\roboto}
\fi


%
% Satzspiegel konstruieren.
%
% Der Satzspiegel ist umschaltbar. Wenn Kopf und Fußzeile angeschaltet werden,
% wird entsprechend mehr Platz vorgesehen. Für die Kopfzeile wird aber nicht
% die Höhe der Kopfzeile umgestellt, sondern der Abstand zum Textbereich.
% Damit ist sichergestellt, dass die Kopfzeilen nicht verschoben werden, wenn
% auf einen der Stadardseitenstile umgestellt wird. Die zu kleine
% Kopfzeilenhöhe kompensieren wir beim zusammensetzen der TUC-Kopfzeile.
%
\newcommand{\tucarticle@head@height}{14.5pt}   % Zeilenhöhe
\newcommand{\tucarticle@head@sep}{14.2pt}      % Standardabstamd
\newcommand{\tucarticle@head@content}{}
\newcommand{\tucarticle@foot@height}{14.5pt}   % Zeilenhöhe
\newcommand{\tucarticle@foot@skip}{34.4pt}     % 14.5pt Zeilenhöhe + 7mm Rand (19.9pt)
\newcommand{\tucarticle@foot@content}{}

% Satzspiegel umschalten. Es wird automatisch ein Seitenumbruch eingefügt.
\newcommand{\tucarticle@updategeometry}{%
%
% Wenn das calc-Paket geladen ist, werden \setlength und \addtolength so
% überschrieben, dass sie nicht mehr in \g@addto@macro funktionieren, was
% wiederum durch \AtNextShipout genutzt wird. Deshalb definieren wir sie auf
% die Standard-LaTeX-Kommandos zurück.
%
\def\setlength##1##2{##1 ##2\relax}
\def\addtolength##1##2{\advance##1 ##2\relax}
%
\newgeometry{
  includeheadfoot,
  inner=25mm,
  outer=20mm,
  top=12mm,
  bottom=10.6mm,
  footskip=\tucarticle@foot@skip,
  headheight=14.5pt,
  headsep=\tucarticle@head@sep,
  nomarginpar
}%
% Verschieben wir die Satzspiegeländerung auf den nächsten Seitenumbruch, dann
% werden wir durch evershi aus \shipout heraus aufgerufen. \shipout wird
% wiederum aus der Ausgaberoutine heraus aufgerufen, die durch TeX in einer
% Gruppe gekapselt wird. Die Zuweisungen von \newgeometry sind daher lokal und
% werden nach der Ausgaberoutine verworfen. Wir setzen daher die von uns
% beeinflussten Längenregister nochmals global.
\global\setlength{\textheight}{\textheight}%
\global\setlength{\textwidth}{\textwidth}%
\global\setlength{\headsep}{\headsep}%
\global\setlength{\footskip}{\footskip}%
\global\setlength{\footheight}{\tucarticle@foot@height}%
\global\addtolength{\footheight}{0.1pt}}

\newcommand{\tucheader}{%
% Einzug von oben:    48mm
% Oberer Rand:       -12mm
% Höhe der Kopfzeile -14.5pt
\global\def\tucarticle@head@sep{87.9pt}%
\tucarticle@updategeometry%
\global\renewcommand{\tucarticle@head@content}{\tucarticle@head@content@block}}

\newcommand{\tucnoheader}{%
\global\def\tucarticle@head@sep{14.5pt}%
\tucarticle@updategeometry%
\global\def\tucarticle@head@content{}}

\newcommand{\tucfooterblock}{%
% Abstand:           7mm
% Höhe der Fußzeile 18mm
\global\def\tucarticle@foot@height{18mm}%
\global\def\tucarticle@foot@skip{25mm}%
\tucarticle@updategeometry%
\global\def\tucarticle@foot@content{\tucarticle@foot@content@block}}

\newcommand{\tucfooterpage}{%
\global\def\tucarticle@foot@height{14.5pt}%
% 14.5pt Zeilenhöhe + 7mm Rand (19.9pt)
\global\def\tucarticle@foot@skip{34.4pt}%
\tucarticle@updategeometry%
\global\def\tucarticle@foot@content{\tucarticle@foot@content@page}}

\newcommand{\tucnofooter}{%
\global\def\tucarticle@foot@height{14.5pt}%
% 14.5pt Zeilenhöhe + 7mm Rand (19.9pt)
\global\def\tucarticle@foot@skip{34.4pt}%
\tucarticle@updategeometry%
\global\def\tucarticle@foot@content{}}


% Satzspiegel mit dem nächsten Seitenumbruch ändern.
\newcommand{\nexttucheader}{\AtNextShipout{\tucheader}}
\newcommand{\nexttucnoheader}{\AtNextShipout{\tucnoheader}}
\newcommand{\nexttucfooterblock}{\AtNextShipout{\tucfooterblock}}
\newcommand{\nexttucfooterpage}{\AtNextShipout{\tucfooterpage}}
\newcommand{\nexttucnofooter}{\AtNextShipout{\tucnofooter}}

% Standard-Satzspiegel einstellen.
\tucheader
\tucfooterpage

% Folgelogos ausschalten.
\iftuc@contlogo
\else
\AtBeginDocument{\nexttucnoheader}
\fi


%
% Layout von Kopf- und Fußzeile festlegen.
%
\RequirePackage{scrlayer-scrpage}

\setkomafont{pageheadfoot}{\relax}
\setkomafont{pagehead}{\relax}
\setkomafont{pagefoot}{\relax}


\DeclareNewLayer
[
  mode=picture,
  head,
  voffset=12mm,
  width=165mm,
  height=0mm,
  align=tl,
  oddpage,
  background,
  contents={\put(\LenToUnit{0mm}, \LenToUnit{0mm}){\makebox(\LenToUnit{165mm}, \LenToUnit{0mm})[lt]{\tucarticle@head@content}}}
]{tuc.head}

\DeclareNewLayer
[
  mode=picture,
  foot,
  voffset=286.4mm,
  width=165mm,
  height=0mm,
  align=bl,
  background,
  contents={\put(\LenToUnit{0mm}, \LenToUnit{0mm}){\parbox[b]{165mm}{\tucarticle@foot@content}}}
]{tuc.foot}

\DeclarePageStyleByLayers{tuc}{tuc.head,tuc.foot}

\pagestyle{tuc}


%
% Seitenkopf
%
\addtokomafont{firstheadline}{\fontsize{12}{19}\selectfont}
\addtokomafont{nextheadline}{\fontsize{12}{19}\selectfont}

% Kopfblock
\newcommand{\tucarticle@head@content@block}{}

\newcommand{\tucarticle@headblock}[2]{%
\begingroup%
\setlength{\unitlength}{1mm}%
\iftuckhs
% Das Logo hat die Abmessungen 39.66 x 23.64mm. Die Höhe ist gleich dem regulären Logo.
\begin{picture}(165, 23.65)(0, -23.65)
\iftuc@head
\put(0, -23.65){\makebox(39.66, 23.65)[l]{\includegraphics[width=39.66mm]{\tuc@logo}\hspace*{10mm}}}%
\fi
% Die Linie hat eine Gesamtlänge von 25mm und damit einen kleinen Überstand nach oben und unten.
\put(49.66, -24.325){#1}
\put(59.66, -23.65){#2}
\end{picture}
\else
\begin{picture}(165, 0)
\iftuc@head
\put(0, -23.65){\makebox(47, 23.65)[l]{\includegraphics[width=47mm]{\tuc@logo}}}
\fi
% Linie hat eine Gesamtlänge von 25mm und damit einen kleinen Überstand nach oben und unten.
\put(57, -24.325){#1}
\put(67, -23.65){#2}
\end{picture}%
\fi%
\endgroup}

% Trennlinie
\newcommand{\tucarticle@head@sepline}{\makebox(0, 25.0)[t]{\hspace*{-0.375pt}\vrule width 0.75pt height 25.0mm}}

% Eine Kopfzeile.
\newcommand{\m@keheadline}[3]{\raisebox{#2}{\rlap{\makebox{\hbox to #1{#3\hfill}}}}}

% Alle 4 Kopfzeilen.
\newcommand{\firstheadline}{\usekomafont{firstheadline}}%
\newcommand{\nextheadline}{\usekomafont{nextheadline}}%
\newcommand{\tucheadlines}[4]{%
\gdef\tucarticle@head@content@block{%
\tucarticle@headblock{\tucarticle@head@sepline}{%
\m@keheadline{98mm}{57pt}{\firstheadline #1}%
\m@keheadline{98mm}{38pt}{\nextheadline #2}%
\m@keheadline{98mm}{19pt}{\nextheadline #3}%
\m@keheadline{98mm}{00pt}{\nextheadline #4}%
}}}

% Beliebiger Text
\newcommand{\tucheadtext}[1]{%
\gdef\tucarticle@head@content@block{%
\tucarticle@headblock{\tucarticle@head@sepline}{%
\begin{minipage}[b][23.65mm][t]{98mm}
#1
\end{minipage}}}}

% Nur ein Logo
\newcommand{\tucheadlogo}{%
\gdef\tucarticle@head@content@block{%
\tucarticle@headblock{}{}}}

% Kein Kopf
\newcommand{\tucheadempty}{%
\gdef\tucarticle@head@content@block{}}

% Im Normalfall nur das Logo anzeigen.
\tucheadlogo


%
% Seitenfuß (Infoblock)
%
\addtokomafont{footline}{\fontsize{8pt}{9.6pt}\selectfont}

\newcommand{\tucarticle@foot@content@block@logo}{}
\newcommand{\tucarticle@foot@content@block@info}{}

% Ein Logo
\newcommand{\tucfootlogo}[1]{%
\gdef\tucarticle@foot@content@block@logo{%
\includegraphics[height=\vsize,width=\hsize,keepaspectratio]{#1}\hspace*{\fill}}}

% Zwei Logos
\newcommand{\tucfoottwologo}[2]{%
\gdef\tucarticle@foot@content@block@logo{%
\begingroup%
\locbox{\logoi}%
\locbox{\logoii}%
\savebox{\logoi}{\includegraphics{#1}}%
\savebox{\logoii}{\includegraphics{#2}}%
\newlength{\l@g@scale}\setlength{\l@g@scale}{\hsize*\ratio{1pt}{1pt*\ratio{\ht\logoi}{\wd\logoi} + 1pt*\ratio{\ht\logoii}{\wd\logoii}}}%
\newlength{\l@g@iwidth}\setlength{\l@g@iwidth}{\l@g@scale*\ratio{\ht\logoii}{\wd\logoii}}%
\newlength{\l@g@iiwidth}\setlength{\l@g@iiwidth}{\l@g@scale*\ratio{\ht\logoi}{\wd\logoi}}%
\(\vcenter{\hbox{\includegraphics[width=0.9\l@g@iwidth,height=\vsize,keepaspectratio]{#1}}}\)%
\hspace*{\fill}%
\(\vcenter{\hbox{\includegraphics[width=0.9\l@g@iiwidth,height=\vsize,keepaspectratio]{#2}}}\)%
\endgroup}}

% Beliebiges Logo
\newcommand{\tucfootcustomlogo}[1]{%
\gdef\tucarticle@foot@content@block@logo{#1}}

% Kein Logo
\newcommand{\tucfootnologo}{%
\gdef\tucarticle@foot@content@block@logo{}}

% Infoblock
\newcommand{\tucfootinfo}[1]{%
\gdef\tucarticle@foot@content@block@info{#1}}

\newcommand{\tucarticle@foot@content@block}{%
\begin{minipage}[b][18mm][b]{\hsize}
\usekomafont{footline}%
\locbox{\footlines}
\savebox{\footlines}{%
\parbox[b]{98mm}{%
\raggedright%
\def\\{~$\cdot$~}%
\setlength{\parskip}{5.3pt}%
\tucarticle@foot@content@block@info%
}}%
\setlength{\vsize}{\ht\footlines}
% Mindestgröße des Logos (4 Fußzeilen + Zwischenraum):
%   8pt + 3 * 9.4pt + 5.3pt = 41.5pt
\ifdim\vsize<41.5pt\setlength{\vsize}{41.5pt}\fi
\begin{minipage}[b][\vsize][c]{57mm}
\tucarticle@foot@content@block@logo
\end{minipage}%
\hfill%
\usebox{\footlines}%
\end{minipage}}


%
% Seitenfuß (Seitenzahl)
%
\AtBeginDocument{\ifcurrentbaselanguage{German}{\newcommand{\ofname}{von}}{\newcommand{\ofname}{of}}}

% scrartcl definiert die Seitenbezeichnung nicht.
\providecommand{\pagename}{Seite}

% Keine Verlinkung, wenn Hyperref geladen ist.
\newcommand{\m@kepage}{\pagename~\thepage\iftuc@totpages~\ofname~\pageref{LastPage}\fi}
\AtBeginDocument{%
  \@ifpackageloaded{hyperref}{%
    \renewcommand{\m@kepage}{\pagename~\thepage\iftuc@totpages~\ofname~\pageref*{LastPage}\fi}%
  }{}%
}

% Seitenzahl
\newcommand{\tucfootpage}{%
\gdef\tucarticle@foot@content@page{\if@twoside\Ifthispageodd{\hfill\m@kepage}{\m@kepage\hfill}\else\hfill\m@kepage\fi}}

% Kein Seitenfuß
\newcommand{\tucfootpageempty}{%
\gdef\tucarticle@foot@content@page{}}

% Im Normalfall Seitenzahlen anzeigen.
\tucfootpage


%
% Verschiedenes
%

% Auf linksbündig umschalten.
\iftuc@flushleft
\AtBeginDocument{\raggedright}
\fi


\endinput
