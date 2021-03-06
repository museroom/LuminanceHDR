/**
 * This file is a part of Luminance HDR package.
 * ----------------------------------------------------------------------
 * Copyright (C) 2006,2007 Giuseppe Rota
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 * ----------------------------------------------------------------------
 *
 * @author Giuseppe Rota <grota@users.sourceforge.net>
 *
 * @author Franco Comida <fcomida@users.sourceforge.net>
 *
 */

#include <QColorDialog>
#include <QFileDialog>
#include <QWhatsThis>
#include <QMessageBox>
#include <QDebug>

#include <iostream>
#include <cmath>

#include "Common/global.h"
#include "Common/config.h"
#include "Common/LuminanceOptions.h"
#include "Common/TranslatorManager.h"
#include "Preferences/PreferencesDialog.h"

// UI
#include "ui_PreferencesDialog.h"

#define KEY_USER_QUAL_TOOLBUTTON "preference_dialog/user_qual_toolButton"
#define KEY_MED_PASSES_TOOLBUTTON "preference_dialog/med_passes_toolButton"
#define KEY_WB_METHOD_TOOLBUTTON "preference_dialog/wb_method_toolButton"
#define KEY_TK_TOOLBUTTON "preference_dialog/TK_toolButton"
#define KEY_MULTIPLIERS_TOOLBUTTON "preference_dialog/multipliers_toolButton"
#define KEY_HIGHLIGHTS_TOOLBUTTON "preference_dialog/highlights_toolButton"
#define KEY_LEVEL_TOOLBUTTON "preference_dialog/level_toolButton"
#define KEY_BRIGHTNESS_TOOLBUTTON "preference_dialog/brightness_toolButton"
#define KEY_USER_BLACK_TOOLBUTTON "preference_dialog/user_black_toolButton"
#define KEY_USER_SAT_TOOLBUTTON "preference_dialog/user_sat_toolButton"
#define KEY_THRESHOLD_TOOLBUTTON "preference_dialog/threshold_toolButton"
#define KEY_RED_TOOLBUTTON "preference_dialog/red_toolButton"
#define KEY_BLUE_TOOLBUTTON "preference_dialog/blue_toolButton"
#define KEY_GREEN_TOOLBUTTON "preference_dialog/green_toolButton"

#ifdef WIN32
	#define ICC_PATH "C:\\WINDOWS\\system32\\spool\\drivers\\color"
#elif defined __APPLE__
	#define ICC_PATH "/Library/ColorSync/Profiles/"
#else
	#define ICC_PATH "/usr/share/color/icc"
#endif

namespace
{
inline double pos2value(int pos, int minpos, int maxpos, double minv, double maxv)
{
    double x = (pos - minpos)/( (double) (maxpos - minpos));
    return minv*exp(log(maxv/minv)*x );
}

inline int value2pos(double value, int minpos, int maxpos, double minv, double maxv)
{
    double y = (log(value)-log(minv))/(log(maxv)-log(minv));
    return (int) ((maxpos - minpos)*y) + minpos;
}

}

PreferencesDialog::PreferencesDialog(QWidget *p):
    QDialog(p),
    m_Ui(new Ui::PreferencesDialog)
{
    m_Ui->setupUi(this);

#ifdef DEMOSAICING_GPL2
	qDebug() << "PreferencesDialog: Found demosaicing pack GPL2";
	m_Ui->user_qual_comboBox->addItem("DCB");
	m_Ui->user_qual_comboBox->addItem("AHD v2");
	m_Ui->user_qual_comboBox->addItem("AFD");
	m_Ui->user_qual_comboBox->addItem("VCD");
	m_Ui->user_qual_comboBox->addItem("VCD & AHD");
	m_Ui->user_qual_comboBox->addItem("LMMSE");
#endif
#ifdef DEMOSAICING_GPL3
	qDebug() << "PreferencesDialog: Found AMaZE";
	m_Ui->user_qual_comboBox->addItem("AMaZE");
#endif

	fromIso639ToGuiIndex["cs"]= 0;
    fromIso639ToGuiIndex["da"]= 1;
	fromIso639ToGuiIndex["de"]= 2;
	fromIso639ToGuiIndex["en"]= 3;
	fromIso639ToGuiIndex["es"]= 4;
	fromIso639ToGuiIndex["fr"]= 5;
	fromIso639ToGuiIndex["id"]= 6;
	fromIso639ToGuiIndex["it"]= 7;
	fromIso639ToGuiIndex["hu"]= 8;
	fromIso639ToGuiIndex["pl"]= 9;
	fromIso639ToGuiIndex["pt_BR"]= 10;
	fromIso639ToGuiIndex["ru"]=11;
	fromIso639ToGuiIndex["ro"]=12;
	fromIso639ToGuiIndex["fi"]=13;
	fromIso639ToGuiIndex["tr"]=14;
	fromIso639ToGuiIndex["zh"]=15;

	fromGuiIndexToIso639[ 0]="cs";
	fromGuiIndexToIso639[ 1]="da";
	fromGuiIndexToIso639[ 2]="de";
	fromGuiIndexToIso639[ 3]="en";
	fromGuiIndexToIso639[ 4]="es";
	fromGuiIndexToIso639[ 5]="fr";
	fromGuiIndexToIso639[ 6]="id";
	fromGuiIndexToIso639[ 7]="it";
	fromGuiIndexToIso639[ 8]="hu";
	fromGuiIndexToIso639[ 9]="pl";
	fromGuiIndexToIso639[10]="pt_BR";
	fromGuiIndexToIso639[11]="ru";
	fromGuiIndexToIso639[12]="ro";
	fromGuiIndexToIso639[13]="fi";
	fromGuiIndexToIso639[14]="tr";
    fromGuiIndexToIso639[15]="zh";

    from_options_to_gui(); //update the gui in order to show the options
    
    toolButtonMapper = new QSignalMapper(this);
    connect(toolButtonMapper, SIGNAL(mapped(int)), this, SLOT(toolButton_clicked(int)));

    QObject* tabEntries[] = {
        m_Ui->toolButtonInterface,
        m_Ui->toolButtonTM,
        m_Ui->toolButtonRAW,
        m_Ui->toolButtonCMS,
        m_Ui->toolButtonExtTool
    };
    for (int i = 0; i < 5; i++)
    {
    	toolButtonMapper->setMapping(tabEntries[i], i);
    	connect(tabEntries[i], SIGNAL(clicked()), toolButtonMapper, SLOT(map()));
    }
}

PreferencesDialog::~PreferencesDialog()
{
	delete toolButtonMapper;
}

void PreferencesDialog::changeEvent(QEvent *event)
{
	if (event->type() == QEvent::LanguageChange)
    {
		 m_Ui->retranslateUi(this);
    }
	QWidget::changeEvent(event);
}

void PreferencesDialog::on_okButton_clicked()
{
    bool restartNeeded = false;

    LuminanceOptions luminance_options;

    if (luminance_options.getGuiLang() != fromGuiIndexToIso639[m_Ui->languageComboBox->currentIndex()])
    {
        luminance_options.setGuiLang( fromGuiIndexToIso639[m_Ui->languageComboBox->currentIndex()] );
        TranslatorManager::setLanguage( luminance_options.getGuiLang() );
    }

    luminance_options.setTempDir( m_Ui->lineEditTempPath->text() );

    luminance_options.setPreviewWidth( m_Ui->previewsWidthSpinBox->value() );
    luminance_options.setPreviewPanelActive( m_Ui->checkBoxTMOWindowsPreviewPanel->isChecked() );

    if (m_Ui->chkPortableMode->isChecked() != LuminanceOptions::isCurrentPortableMode)
    {
        restartNeeded = true;
        luminance_options.setPortableMode(m_Ui->chkPortableMode->isChecked());
    }

    // --- Batch TM
    luminance_options.setBatchTmNumThreads( m_Ui->numThreadspinBox->value() );

    // --- Other Parameters

    QStringList ais_options = m_Ui->aisParamsLineEdit->text().split(" ",QString::SkipEmptyParts);
    luminance_options.setAlignImageStackOptions(ais_options, true);

    // --- RAW parameters
    luminance_options.setRawFourColorRGB( m_Ui->four_color_rgb_CB->isChecked() );
    luminance_options.setRawDoNotUseFujiRotate( m_Ui->do_not_use_fuji_rotate_CB->isChecked() );
	QString user_qual = m_Ui->user_qual_comboBox->itemText( m_Ui->user_qual_comboBox->currentIndex() );
	if (user_qual == "Bilinear" ||
		user_qual == "VNG" ||
		user_qual == "PPG" ||
		user_qual == "AHD") 
			luminance_options.setRawUserQuality( m_Ui->user_qual_comboBox->currentIndex() );
	else if(user_qual == "DCB")
			luminance_options.setRawUserQuality( 4 );
	else if(user_qual == "AHD v2")
			luminance_options.setRawUserQuality( 5 );
	else if(user_qual == "AFD")
			luminance_options.setRawUserQuality( 6 );
	else if(user_qual == "VCD")
			luminance_options.setRawUserQuality( 7 );
	else if(user_qual == "VCD & AHD")
			luminance_options.setRawUserQuality( 8 );
	else if(user_qual == "LMMSE")
			luminance_options.setRawUserQuality( 9 );
	else if(user_qual == "AMaZE")
			luminance_options.setRawUserQuality( 10 );
    luminance_options.setRawMedPasses( m_Ui->med_passes_spinBox->value() );
    luminance_options.setRawWhiteBalanceMethod( m_Ui->wb_method_comboBox->currentIndex() );
    luminance_options.setRawTemperatureKelvin( m_Ui->TK_spinBox->value() );
    luminance_options.setRawGreen( m_Ui->green_doubleSpinBox->value() );
    luminance_options.setRawHighlightsMode( m_Ui->highlights_comboBox->currentIndex() );
    luminance_options.setRawLevel( m_Ui->level_spinBox->value() );
    luminance_options.setRawAutoBrightness( m_Ui->auto_bright_CB->isChecked() );
    luminance_options.setRawBrightness( m_Ui->brightness_doubleSpinBox->value() );
    luminance_options.setRawUseBlack( m_Ui->use_black_CB->isChecked() );
    luminance_options.setRawUseSaturation( m_Ui->use_sat_CB->isChecked() );
    luminance_options.setRawUseNoiseReduction( m_Ui->use_noise_CB->isChecked() );
    luminance_options.setRawUseChromaAber( m_Ui->use_chroma_CB->isChecked() );
    luminance_options.setRawNoiseReductionThreshold( m_Ui->threshold_spinBox->value() );
    luminance_options.setRawUserBlack( m_Ui->user_black_spinBox->value() );
    luminance_options.setRawUserSaturation( m_Ui->user_sat_spinBox->value() );
    luminance_options.setRawAber0( m_Ui->red_doubleSpinBox->value() );
    luminance_options.setRawAber2( m_Ui->blue_doubleSpinBox->value() );

	// --- Color Management
	luminance_options.setCameraProfileFileName( m_Ui->camera_lineEdit->text() );
	luminance_options.setMonitorProfileFileName( m_Ui->monitor_lineEdit->text() );
	luminance_options.setPrinterProfileFileName( m_Ui->printer_lineEdit->text() );

    // ---- temporary... this rubbish must go away!
    luminance_options.setValue(KEY_USER_QUAL_TOOLBUTTON, m_Ui->user_qual_toolButton->isEnabled());
    luminance_options.setValue(KEY_MED_PASSES_TOOLBUTTON, m_Ui->med_passes_toolButton->isEnabled());
    luminance_options.setValue(KEY_WB_METHOD_TOOLBUTTON, m_Ui->wb_method_toolButton->isEnabled());
    luminance_options.setValue(KEY_TK_TOOLBUTTON, m_Ui->TK_toolButton->isEnabled());
    luminance_options.setValue(KEY_HIGHLIGHTS_TOOLBUTTON, m_Ui->highlights_toolButton->isEnabled());
    luminance_options.setValue(KEY_LEVEL_TOOLBUTTON, m_Ui->level_toolButton->isEnabled());
    luminance_options.setValue(KEY_BRIGHTNESS_TOOLBUTTON, m_Ui->brightness_toolButton->isEnabled());
    luminance_options.setValue(KEY_USER_BLACK_TOOLBUTTON, m_Ui->user_black_toolButton->isEnabled());
    luminance_options.setValue(KEY_USER_SAT_TOOLBUTTON, m_Ui->user_sat_toolButton->isEnabled());
    luminance_options.setValue(KEY_THRESHOLD_TOOLBUTTON, m_Ui->threshold_toolButton->isEnabled());
    luminance_options.setValue(KEY_RED_TOOLBUTTON, m_Ui->red_toolButton->isEnabled());
    luminance_options.setValue(KEY_BLUE_TOOLBUTTON, m_Ui->blue_toolButton->isEnabled());
    luminance_options.setValue(KEY_GREEN_TOOLBUTTON, m_Ui->green_toolButton->isEnabled());

    if (restartNeeded)
    {
        QMessageBox::information(this, tr("Restart"), tr("For the settings to take effect, please restart the application!"));
    }
    accept();
}

void PreferencesDialog::on_cancelButton_clicked()
{
	reject();
}

void PreferencesDialog::on_user_qual_comboBox_currentIndexChanged(int value)
{
	m_Ui->user_qual_toolButton->setEnabled(value != 0);
}

void PreferencesDialog::on_med_passes_spinBox_valueChanged(int value)
{
    m_Ui->med_passes_toolButton->setEnabled(value != 0);
}

void PreferencesDialog::on_wb_method_comboBox_currentIndexChanged(int i)
{
	bool isManualWb = i == 3;
    m_Ui->TK_label->setEnabled(isManualWb);
    m_Ui->TK_horizontalSlider->setEnabled(isManualWb);
    m_Ui->TK_spinBox->setEnabled(isManualWb);
    m_Ui->green_label->setEnabled(isManualWb);
    m_Ui->green_horizontalSlider->setEnabled(isManualWb);
    m_Ui->green_doubleSpinBox->setEnabled(isManualWb);

    m_Ui->wb_method_toolButton->setEnabled(i != 1);
}

void PreferencesDialog::on_TK_spinBox_valueChanged(int value)
{
    m_Ui->TK_toolButton->setEnabled(value != false);
}

void PreferencesDialog::on_highlights_comboBox_currentIndexChanged(int i)
{
    m_Ui->highlights_toolButton->setEnabled(i != 0);
}

void PreferencesDialog::on_level_spinBox_valueChanged(int value)
{
    m_Ui->level_toolButton->setEnabled(value != 0);
}

void PreferencesDialog::on_user_black_spinBox_valueChanged(int value)
{
    m_Ui->user_black_toolButton->setEnabled(value != 0);
}

void PreferencesDialog::on_user_sat_spinBox_valueChanged(int value)
{
	m_Ui->user_sat_toolButton->setEnabled(value != 20000);
}

void PreferencesDialog::on_threshold_spinBox_valueChanged(int value)
{
    m_Ui->threshold_toolButton->setEnabled(value != 100);
}

void PreferencesDialog::on_use_black_CB_stateChanged(int)
{
	bool checked = m_Ui->use_black_CB->isChecked();
    m_Ui->user_black_horizontalSlider->setEnabled(checked);
    m_Ui->user_black_spinBox->setEnabled(checked);
}

void PreferencesDialog::on_use_sat_CB_stateChanged(int) {
	bool checked = m_Ui->use_sat_CB->isChecked();
	m_Ui->user_sat_horizontalSlider->setEnabled(checked);
	m_Ui->user_sat_spinBox->setEnabled(checked);
}

void PreferencesDialog::on_use_noise_CB_stateChanged(int)
{
	bool checked = m_Ui->use_noise_CB->isChecked();
	m_Ui->threshold_label->setEnabled(checked);
	m_Ui->threshold_horizontalSlider->setEnabled(checked);
	m_Ui->threshold_spinBox->setEnabled(checked);
}

void PreferencesDialog::on_use_chroma_CB_stateChanged(int)
{
	bool checked = m_Ui->use_chroma_CB->isChecked();
	m_Ui->red_label->setEnabled(checked);
	m_Ui->red_horizontalSlider->setEnabled(checked);
	m_Ui->red_doubleSpinBox->setEnabled(checked);
	m_Ui->blue_label->setEnabled(checked);
	m_Ui->blue_horizontalSlider->setEnabled(checked);
	m_Ui->blue_doubleSpinBox->setEnabled(checked);
}

void PreferencesDialog::on_brightness_horizontalSlider_valueChanged(int value)
{
    m_Ui->brightness_doubleSpinBox->setValue(((double) value)/m_Ui->brightness_doubleSpinBox->maximum());
}

void PreferencesDialog::on_brightness_doubleSpinBox_valueChanged(double value)
{
    m_Ui->brightness_horizontalSlider->setValue((int) (value*m_Ui->brightness_doubleSpinBox->maximum()));
	m_Ui->brightness_toolButton->setEnabled(fabs(value - 1.0) >= 1e-4);
}

void PreferencesDialog::on_red_horizontalSlider_valueChanged(int pos)
{
    int minpos = m_Ui->red_horizontalSlider->minimum();
    int maxpos = m_Ui->red_horizontalSlider->maximum();
    double minv = m_Ui->red_doubleSpinBox->minimum();
    double maxv = m_Ui->red_doubleSpinBox->maximum();

    m_Ui->red_doubleSpinBox->setValue( pos2value(pos, minpos, maxpos, minv, maxv) );
}

void PreferencesDialog::on_red_doubleSpinBox_valueChanged(double value)
{
    int minpos = m_Ui->red_horizontalSlider->minimum();
    int maxpos = m_Ui->red_horizontalSlider->maximum();
    double minv = m_Ui->red_doubleSpinBox->minimum();
    double maxv = m_Ui->red_doubleSpinBox->maximum();

    m_Ui->red_horizontalSlider->setValue( value2pos(value, minpos, maxpos, minv, maxv) );
    m_Ui->red_toolButton->setEnabled(fabs(value - 1.0) >= 1e-4);
}

void PreferencesDialog::on_blue_horizontalSlider_valueChanged(int pos)
{
    int minpos = m_Ui->blue_horizontalSlider->minimum();
    int maxpos = m_Ui->blue_horizontalSlider->maximum();
    double minv = m_Ui->blue_doubleSpinBox->minimum();
    double maxv = m_Ui->blue_doubleSpinBox->maximum();

    m_Ui->blue_doubleSpinBox->setValue( pos2value(pos, minpos, maxpos, minv, maxv) );
}

void PreferencesDialog::on_blue_doubleSpinBox_valueChanged(double value)
{
    int minpos = m_Ui->blue_horizontalSlider->minimum();
    int maxpos = m_Ui->blue_horizontalSlider->maximum();
    double minv = m_Ui->blue_doubleSpinBox->minimum();
    double maxv = m_Ui->blue_doubleSpinBox->maximum();

    m_Ui->blue_horizontalSlider->setValue( value2pos(value, minpos, maxpos, minv, maxv) );
	m_Ui->blue_toolButton->setEnabled(fabs(value - 1.0) >= 1e-4);
}

void PreferencesDialog::on_green_horizontalSlider_valueChanged( int pos)
{
    int minpos = m_Ui->green_horizontalSlider->minimum();
    int maxpos = m_Ui->green_horizontalSlider->maximum();
    double minv = m_Ui->green_doubleSpinBox->minimum();
    double maxv = m_Ui->green_doubleSpinBox->maximum();

    m_Ui->green_doubleSpinBox->setValue( pos2value(pos, minpos, maxpos, minv, maxv) );
}

void PreferencesDialog::on_green_doubleSpinBox_valueChanged( double value)
{
    int minpos = m_Ui->green_horizontalSlider->minimum();
    int maxpos = m_Ui->green_horizontalSlider->maximum();
    double minv = m_Ui->green_doubleSpinBox->minimum();
    double maxv = m_Ui->green_doubleSpinBox->maximum();

    m_Ui->blue_horizontalSlider->setValue( value2pos(value, minpos, maxpos, minv, maxv) );
	m_Ui->green_toolButton->setEnabled(fabs(value - 1.0) >= 1e-4);
}

void PreferencesDialog::on_user_qual_toolButton_clicked()
{
	m_Ui->user_qual_comboBox->setCurrentIndex(0);
}

void PreferencesDialog::on_med_passes_toolButton_clicked()
{
    m_Ui->med_passes_horizontalSlider->setValue(0);
    m_Ui->med_passes_spinBox->setValue(0);
    m_Ui->med_passes_toolButton->setEnabled(false);
}

void PreferencesDialog::on_wb_method_toolButton_clicked()
{
    m_Ui->wb_method_comboBox->setCurrentIndex(1);
    m_Ui->wb_method_toolButton->setEnabled(false);
}

void PreferencesDialog::on_TK_toolButton_clicked()
{
    m_Ui->TK_horizontalSlider->setValue(6500);
    m_Ui->TK_spinBox->setValue(6500);
    m_Ui->TK_toolButton->setEnabled(false);
}

void PreferencesDialog::on_highlights_toolButton_clicked()
{
    m_Ui->highlights_comboBox->setCurrentIndex(0);
    m_Ui->highlights_toolButton->setEnabled(false);
}

void PreferencesDialog::on_level_toolButton_clicked()
{
    m_Ui->level_horizontalSlider->setValue(0);
    m_Ui->level_spinBox->setValue(0);
    m_Ui->level_toolButton->setEnabled(false);
}

void PreferencesDialog::on_brightness_toolButton_clicked()
{
    m_Ui->brightness_horizontalSlider->setValue(10);
    m_Ui->brightness_doubleSpinBox->setValue(1.0);
    m_Ui->brightness_toolButton->setEnabled(false);
}

void PreferencesDialog::on_user_black_toolButton_clicked()
{
    m_Ui->user_black_horizontalSlider->setValue(0);
    m_Ui->user_black_spinBox->setValue(0);
    m_Ui->user_black_toolButton->setEnabled(false);
}

void PreferencesDialog::on_user_sat_toolButton_clicked()
{
    m_Ui->user_sat_horizontalSlider->setValue(20000);
    m_Ui->user_sat_spinBox->setValue(20000);
    m_Ui->user_sat_toolButton->setEnabled(false);
}

void PreferencesDialog::on_threshold_toolButton_clicked()
{
    m_Ui->use_noise_CB->setChecked(true);
    m_Ui->threshold_horizontalSlider->setValue(100);
    m_Ui->threshold_spinBox->setValue(100);
    m_Ui->threshold_toolButton->setEnabled(false);
}

void PreferencesDialog::on_red_toolButton_clicked()
{
    int minpos = m_Ui->red_horizontalSlider->minimum();
    int maxpos = m_Ui->red_horizontalSlider->maximum();
    double minv = m_Ui->red_doubleSpinBox->minimum();
    double maxv = m_Ui->red_doubleSpinBox->maximum();

    m_Ui->red_horizontalSlider->setValue( value2pos(1.0, minpos, maxpos, minv, maxv) );
    m_Ui->red_doubleSpinBox->setValue(1.0);
    m_Ui->red_toolButton->setEnabled(false);
}

void PreferencesDialog::on_blue_toolButton_clicked()
{
    int minpos = m_Ui->blue_horizontalSlider->minimum();
    int maxpos = m_Ui->blue_horizontalSlider->maximum();
    double minv = m_Ui->blue_doubleSpinBox->minimum();
    double maxv = m_Ui->blue_doubleSpinBox->maximum();

    m_Ui->blue_horizontalSlider->setValue( value2pos(1.0, minpos, maxpos, minv, maxv) );
    m_Ui->blue_doubleSpinBox->setValue(1.0);
    m_Ui->blue_toolButton->setEnabled(false);
}

void PreferencesDialog::on_green_toolButton_clicked()
{
    int minpos = m_Ui->green_horizontalSlider->minimum();
    int maxpos = m_Ui->green_horizontalSlider->maximum();
    double minv = m_Ui->green_doubleSpinBox->minimum();
    double maxv = m_Ui->green_doubleSpinBox->maximum();

    m_Ui->green_horizontalSlider->setValue( value2pos(1.0, minpos, maxpos, minv, maxv) );
    m_Ui->green_doubleSpinBox->setValue(1.0);
    m_Ui->green_toolButton->setEnabled(false);
}

void PreferencesDialog::toolButton_clicked(int index)
{
    m_Ui->stackedPagesWidget->setCurrentIndex(index);
}

void PreferencesDialog::from_options_to_gui()
{
    LuminanceOptions luminance_options;

    //language: if by any chance luminance_options.gui_lang does NOT contain one of the valid 2 chars
    //codes which are key for the fromIso639ToGuiIndex QMap, provide the default "en"
    if (!fromIso639ToGuiIndex.contains(luminance_options.getGuiLang()))
    {
        luminance_options.setGuiLang("en");
    }
    m_Ui->languageComboBox->setCurrentIndex(fromIso639ToGuiIndex.value(luminance_options.getGuiLang()));

    // Temp directory
    m_Ui->lineEditTempPath->setText(luminance_options.getTempDir());


    m_Ui->numThreadspinBox->setValue( luminance_options.getBatchTmNumThreads() );

    m_Ui->aisParamsLineEdit->setText( luminance_options.getAlignImageStackOptions().join(" ") );

    m_Ui->previewsWidthSpinBox->setValue( luminance_options.getPreviewWidth() );

    m_Ui->checkBoxTMOWindowsPreviewPanel->setChecked(luminance_options.isPreviewPanelActive());

    m_Ui->chkPortableMode->setChecked(LuminanceOptions::isCurrentPortableMode);

    QFile file(QDir(QApplication::applicationDirPath()).filePath(".write"));
    bool dirWritable = file.open(QIODevice::ReadWrite);
    if (dirWritable)
        file.remove();
    m_Ui->chkPortableMode->setEnabled(dirWritable);

    // RAW Processing
    m_Ui->four_color_rgb_CB->setChecked(luminance_options.isRawFourColorRGB());
    m_Ui->do_not_use_fuji_rotate_CB->setChecked(luminance_options.isRawDoNotUseFujiRotate());

#ifdef DEMOSAICING_GPL2
	bool GPL2 = true;
#else
	bool GPL2 = false;
#endif
#ifdef DEMOSAICING_GPL3
	bool GPL3 = true;
#else
	bool GPL3 = false;
#endif

	int user_quality = luminance_options.getRawUserQuality();
	if (user_quality < 4)	
    	m_Ui->user_qual_comboBox->setCurrentIndex( user_quality );
	else if ((GPL2 && GPL3) || (GPL2 && !GPL3)) // We have both demosaicing packs or only GPL2
		m_Ui->user_qual_comboBox->setCurrentIndex( user_quality );
	else // We have only GPL3
		m_Ui->user_qual_comboBox->setCurrentIndex( 4 );

    m_Ui->user_qual_comboBox->setCurrentIndex(luminance_options.getRawUserQuality());
    m_Ui->med_passes_horizontalSlider->setValue(luminance_options.getRawMedPasses());
    m_Ui->med_passes_spinBox->setValue(luminance_options.getRawMedPasses());
    m_Ui->wb_method_comboBox->setCurrentIndex(luminance_options.getRawWhiteBalanceMethod());

    m_Ui->TK_horizontalSlider->setValue(luminance_options.getRawTemperatureKelvin());
    m_Ui->TK_spinBox->setValue(luminance_options.getRawTemperatureKelvin());
    m_Ui->highlights_comboBox->setCurrentIndex(luminance_options.getRawHighlightsMode());
    m_Ui->level_horizontalSlider->setValue(luminance_options.getRawLevel());
    m_Ui->level_spinBox->setValue(luminance_options.getRawLevel());
    //m_Ui->false_colors_CB->setChecked(luminance_options.false_colors);
    m_Ui->auto_bright_CB->setChecked(luminance_options.isRawAutoBrightness());
    m_Ui->brightness_horizontalSlider->setValue((int) 10.0*luminance_options.getRawBrightness());
    m_Ui->brightness_doubleSpinBox->setValue(luminance_options.getRawBrightness());
    m_Ui->use_black_CB->setChecked(luminance_options.isRawUseBlack());

    m_Ui->user_black_horizontalSlider->setValue(luminance_options.getRawUserBlack());
    m_Ui->user_black_spinBox->setValue(luminance_options.getRawUserBlack());
    m_Ui->use_sat_CB->setChecked(luminance_options.isRawUseSaturation());

    m_Ui->user_sat_horizontalSlider->setValue(luminance_options.getRawUserSaturation());
    m_Ui->user_sat_spinBox->setValue(luminance_options.getRawUserSaturation());
    m_Ui->use_noise_CB->setChecked(luminance_options.isRawUseNoiseReduction());

    m_Ui->threshold_horizontalSlider->setValue( luminance_options.getRawNoiseReductionThreshold() );
    m_Ui->threshold_spinBox->setValue( luminance_options.getRawNoiseReductionThreshold() );
    m_Ui->use_chroma_CB->setChecked( luminance_options.isRawUseChromaAber() );

    double r_minv = m_Ui->red_doubleSpinBox->minimum();
    double r_maxv = m_Ui->red_doubleSpinBox->maximum();
    double r_minpos = m_Ui->red_horizontalSlider->minimum();
    double r_maxpos = m_Ui->red_horizontalSlider->maximum();
    double b_minv = m_Ui->blue_doubleSpinBox->minimum();
    double b_maxv = m_Ui->blue_doubleSpinBox->maximum();
    double b_minpos = m_Ui->blue_horizontalSlider->minimum();
    double b_maxpos = m_Ui->blue_horizontalSlider->maximum();
    double g_minv = m_Ui->green_doubleSpinBox->minimum();
    double g_maxv = m_Ui->green_doubleSpinBox->maximum();
    double g_minpos = m_Ui->green_horizontalSlider->minimum();
    double g_maxpos = m_Ui->green_horizontalSlider->maximum();

    m_Ui->red_horizontalSlider->setValue(value2pos(luminance_options.getRawAber0(), r_minpos, r_maxpos, r_minv, r_maxv));
    m_Ui->red_doubleSpinBox->setValue(luminance_options.getRawAber0());
    m_Ui->blue_horizontalSlider->setValue(value2pos(luminance_options.getRawAber2(), b_minpos, b_maxpos, b_minv, b_maxv));
    m_Ui->blue_doubleSpinBox->setValue(luminance_options.getRawAber2());
    m_Ui->green_horizontalSlider->setValue(value2pos(luminance_options.getRawGreen(), g_minpos, g_maxpos, g_minv, g_maxv));
    m_Ui->green_doubleSpinBox->setValue(luminance_options.getRawGreen());

    m_Ui->user_qual_toolButton->setEnabled( luminance_options.value(KEY_USER_QUAL_TOOLBUTTON).toBool());
    m_Ui->med_passes_toolButton->setEnabled( luminance_options.value(KEY_MED_PASSES_TOOLBUTTON).toBool());
    m_Ui->wb_method_toolButton->setEnabled( luminance_options.value(KEY_WB_METHOD_TOOLBUTTON).toBool());
    m_Ui->TK_toolButton->setEnabled( luminance_options.value(KEY_TK_TOOLBUTTON).toBool());
    m_Ui->highlights_toolButton->setEnabled( luminance_options.value(KEY_HIGHLIGHTS_TOOLBUTTON).toBool());
    m_Ui->level_toolButton->setEnabled( luminance_options.value(KEY_LEVEL_TOOLBUTTON).toBool());
    m_Ui->brightness_toolButton->setEnabled( luminance_options.value(KEY_BRIGHTNESS_TOOLBUTTON).toBool());
    m_Ui->user_black_toolButton->setEnabled( luminance_options.value(KEY_USER_BLACK_TOOLBUTTON).toBool());
    m_Ui->user_sat_toolButton->setEnabled( luminance_options.value(KEY_USER_SAT_TOOLBUTTON).toBool());
    m_Ui->threshold_toolButton->setEnabled( luminance_options.value(KEY_THRESHOLD_TOOLBUTTON).toBool());
    m_Ui->red_toolButton->setEnabled( luminance_options.value(KEY_RED_TOOLBUTTON).toBool());
    m_Ui->blue_toolButton->setEnabled( luminance_options.value(KEY_BLUE_TOOLBUTTON).toBool());
    m_Ui->green_toolButton->setEnabled( luminance_options.value(KEY_GREEN_TOOLBUTTON).toBool());
	
	m_Ui->camera_lineEdit->setText( luminance_options.getCameraProfileFileName() );
	m_Ui->monitor_lineEdit->setText( luminance_options.getMonitorProfileFileName() );
	m_Ui->printer_lineEdit->setText( luminance_options.getPrinterProfileFileName() );
}

void PreferencesDialog::on_chooseCachePathButton_clicked()
{
    QString dir = QFileDialog::getExistingDirectory(this,
		tr("Choose a directory"),
		QDir::currentPath(),
		QFileDialog::ShowDirsOnly|QFileDialog::DontResolveSymlinks
	);
    if (!dir.isEmpty())
    {
        m_Ui->lineEditTempPath->setText(dir);
    }
}

void PreferencesDialog::enterWhatsThis()
{
	QWhatsThis::enterWhatsThisMode();
}

void PreferencesDialog::on_camera_pushButton_clicked()
{
    openColorProfile(m_Ui->camera_lineEdit);
}

void PreferencesDialog::on_monitor_pushButton_clicked()
{
    openColorProfile(m_Ui->monitor_lineEdit);
}

void PreferencesDialog::on_printer_pushButton_clicked()
{
    openColorProfile(m_Ui->printer_lineEdit);
}

void PreferencesDialog::openColorProfile(QLineEdit* lineEdit)
{
    QString fileName = QFileDialog::getOpenFileName(this, tr("Open ICC Profile"),
		ICC_PATH,
		tr("Color profile (*.icc *.ICC *.icm *.ICM)")
	);
	if (!fileName.isEmpty())
		lineEdit->setText(fileName);
}
